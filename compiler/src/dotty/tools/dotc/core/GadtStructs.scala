package dotty.tools.dotc.core

import Decorators.*
import Contexts.*
import Types.*
import Symbols.*
import Variances.*
import Names.*
import Flags.*
import GadtUtils.*
import NameKinds.DepParamName
import dotty.tools.dotc.printing.*
import Texts.*
import dotty.tools.dotc.config
import dotty.tools.dotc.config.Printers.{gadts, gadtsConstr}

import scala.collection.mutable

object UnionFind:
  opaque type ECH = Int

  extension (ech: ECH)
    def hash: Int = java.util.Objects.hash(ech)
    def toInt: Int = ech

  // TODO: No better way to do so ??

  final case class UnionFind private(
    private val elems: mutable.ArrayBuffer[Int],
    private val sizes: mutable.ArrayBuffer[Int],
  ):
    def this() = this(mutable.ArrayBuffer.empty, mutable.ArrayBuffer.empty)

    def fresh: UnionFind =
      new UnionFind(elems.clone, sizes.clone)

    def membersOf(ec: ECH): Set[ECH] =
      val repr = find(ec)
      elems.foldLeft(Set(repr))((acc, cand) => if find(cand) == repr then acc + cand else acc)

    def add(): ECH =
      // TODO: Fresh id gen ok?
      val newElem = elems.size
      elems += newElem
      sizes += 1
      newElem

    def union(lhs: ECH, rhs: ECH): ECH =
      val lhs1 = find(lhs)
      val rhs1 = find(rhs)
      if sizes(lhs1) < sizes(rhs1) then
        elems(lhs1) = rhs1
        sizes(rhs1) += sizes(lhs1)
        rhs1
      else
        elems(rhs1) = lhs1
        sizes(lhs1) += sizes(rhs1)
        lhs1

    def find(i: ECH): ECH =
      var p = elems(i)
      while p != elems(p) do
        elems(p) = elems(elems(p))
        p = elems(p)
      p

import UnionFind.*

final case class GSub private(
  val edges: mutable.Map[ECH, mutable.Set[ECH]],
  val revEdges: mutable.Map[ECH, mutable.Set[ECH]]):

  def this() = this(mutable.Map.empty, mutable.Map.empty)

  def fresh: GSub =
    new GSub(clonedBag(edges), clonedBag(revEdges))

  def directLowerBounds(a: ECH): Set[ECH] =
    revEdges.getOrElse(a, Set.empty).toSet

  def directUpperBounds(a: ECH): Set[ECH] =
    edges.getOrElse(a, Set.empty).toSet

  def strictLowerBounds(a: ECH): Set[ECH] =
    dfs(a, revEdges) - a

  def strictUpperBounds(a: ECH): Set[ECH] =
    dfs(a, edges) - a

  def addIneq(a: ECH, b: ECH): Unit =
    //    println(s"WE ADD $a <: $b  CURRENTLY")
    //    println(debugString)
    assert(chain(b, a).isEmpty)
    val es1 = edges.getOrElseUpdate(a, mutable.Set.empty)
    es1 += b
    val es2 = revEdges.getOrElseUpdate(b, mutable.Set.empty)
    es2 += a
  //    println(s"NOW HAVE")
  //    println(debugString)

  def removeIneq(a: ECH, b: ECH): Unit =
    // assert(edges.contains(a) == edges.contains(b)) TODO: ???
    if edges.contains(a) then
      edges(a) -= b
    if revEdges.contains(b) then
      revEdges(b) -= a

  def remove(a: ECH): Unit =
    edges -= a
    edges.values.foreach(_ -= a)
    revEdges -= a
    revEdges.values.foreach(_ -= a)

  def containsEdge(a: ECH, b: ECH): Boolean =
    edges.get(a).map(_.contains(b)).getOrElse(false)

  def merge(a: ECH, b: ECH, ab: ECH): Unit =
//    println(s"MERGE GSUB OF $a AND $b INTO $ab   WHERE")
//    println(debugString)
    assert(chain(a, b).nonEmpty || chain(b, a).nonEmpty)
    // TODO: check this
    val allLower = strictLowerBounds(a) ++ strictLowerBounds(b) + a + b
    val allUpper = strictUpperBounds(a) ++ strictUpperBounds(b) + a + b
    val forward = allLower.flatMap(l => allUpper.map(u => (l, u)))
      .filterNot((l, u) =>
        // TODO: OK?
        (u == ab && containsEdge(l, a) && containsEdge(l, b)) ||
          (l == ab && containsEdge(a, u) && containsEdge(b, u))
      )
    val lower = revEdges.getOrElse(a, mutable.Set.empty).toSet.filter(_ != b)
      ++ revEdges.getOrElse(b, mutable.Set.empty).toSet.filter(_ != a)
    val upper = edges.getOrElse(a, mutable.Set.empty).toSet.filter(_ != b)
      ++ edges.getOrElse(b, mutable.Set.empty).toSet.filter(_ != a)
    val extra = lower.map(l => (l, ab)) ++ upper.map(u => (ab, u))

    remove(a)
    remove(b)
    forward.foreach((v1, v2) => removeIneq(v1, v2))
//    println("LOWER: "+lower)
//    println("UPPER: "+upper)
//    println("FWD: "+forward)
    // TODO
    //    (extra -- forward).foreach((v1, v2) => addIneq(v1, v2))
    extra.foreach((v1, v2) => addIneq(v1, v2))
//    println("WE NOW HAVE:")
//    println(debugString)

  private def dfs(from: ECH, theEdges: mutable.Map[ECH, mutable.Set[ECH]]): Set[ECH] =
    val stack = mutable.Stack.fill(1)(from)
    val seen = mutable.Set.empty[ECH]
    while stack.nonEmpty do
      val v = stack.pop()
      if !seen.contains(v) then
        seen += v
        theEdges.getOrElse(v, mutable.ArrayBuffer.empty)
          .foreach(stack.push)
    seen.toSet

  def chain(from: ECH, to: ECH): Option[Seq[ECH]] =
    val stack = mutable.Stack((from, Seq(from)))
    val seen = mutable.Set.empty[ECH]
    //    println(s"CHAIN $from TO $to  KNOWING THAT:")
    //    println(debugString)
    while stack.nonEmpty do
      val (v, paths) = stack.pop()
      assert(paths.last == v)
      if v == to then
      //        println(s"YES: $paths")
        return Some(paths)
      if !seen.contains(v) then
        seen += v
        edges.get(v).foreach(
          _.foreach(next => stack.push((next, paths :+ next))))
    //    println("NOPE")
    None

  def debugString: String =
    if edges.isEmpty then
      "(empty gsub)"
    else
      edges.foldLeft(Seq.empty[String]) {
        case (acc, (ec, his)) =>
          acc :+ s"""[$ec] <: {${his.map(hi => s"[$hi]").mkString(", ")}}"""
      }.mkString("\n")


opaque type TH = Int

object TH:
  def fromInt(v: Int): TH = v

extension (th: TH)
  def toInt: Int = th


final case class Knowledge private(
  // TODO: If adding fields, remember to updade merge if needed
  private val unionFind: UnionFind,
  private val gSub: GSub,
  private var thCounter: Int,
  private val members: mutable.Map[ECH, mutable.Set[TH]],
  private val revMembers: mutable.Map[TH, ECH],
  private val storedTypes: mutable.Map[TH, Type],
  private val dets: mutable.Map[ECH, TH],
  private val typeVarReprs: mutable.Map[ECH, TypeVar],
  private val revTypeVarReprs: mutable.Map[TypeVar, ECH],
  private val ext2int: mutable.Map[TypeVar, TypeVar],
  private val int2ext: mutable.Map[TypeVar, TypeVar],
  val symsEC: mutable.Map[Symbol, ECH],
  private var origCstrt: OrderingConstraint):

  def this() = this(
    new UnionFind,
    new GSub,
    0,
    mutable.Map.empty,
    mutable.Map.empty,
    mutable.Map.empty,
    mutable.Map.empty,
    mutable.Map.empty,
    mutable.Map.empty,
    mutable.Map.empty,
    mutable.Map.empty,
    mutable.Map.empty,
    OrderingConstraint.empty)

  def fresh: Knowledge =
    val res = new Knowledge(
      unionFind.fresh,
      gSub.fresh,
      thCounter,
      clonedBag(members),
      revMembers.clone,
      storedTypes.clone,
      dets.clone,
      typeVarReprs.clone,
      revTypeVarReprs.clone,
      ext2int.clone,
      int2ext.clone,
      symsEC.clone,
      origCstrt)
    assert(res == this)
    res

  def isEmpty: Boolean = members.isEmpty

  //////////////////////////////////////////////////////////////////////

  private object AsEC:
    private def typeVarToEC(tv: TypeVar): Option[ECH] =
      revTypeVarReprs.get(tv)
        .orElse(ext2int.get(tv).map(revTypeVarReprs))
        .map(unionFind.find)

    def unapply(t: Type)(using Context): Option[ECH] =
      t match
        case tv: TypeVar => typeVarToEC(tv)
        case HKTypeLambda(params, AppliedType(tv: TypeVar, args))
        if params.corresponds(args)((param, arg) => param.paramRef == arg) =>
          typeVarToEC(tv)
        case _ => None

  private object AsAppliedEC:
    def unapply(t: Type)(using Context): Option[(ECH, List[Type])] =
      t match
        case AppliedType(AsEC(ec), args) => Some((ec, args))
        case _ => None

  private object AsClassOrTrait:
    def unapply(t: Type)(using Context): Option[(ClassSymbol, List[Type])] =
      t match
        case tr: TypeRef if tr.symbol.isClass =>
          Some((tr.symbol.asClass, Nil))
        case AppliedType(tr: TypeRef, args) if tr.symbol.isClass =>
          Some((tr.symbol.asClass, args))
        case _ => None

  //////////////////////////////////////////////////////////////////////

  def allMembers: Set[TH] =
    members.values.flatMap(_.toSet).toSet

  def weaklyDetsOf(a: ECH)(using Context): Set[Type] =
    members(a).toSet.map(storedTypes).filter(isWeaklyDet)

  def removeMember(th: TH): Unit =
    val ec = revMembers(th)
    revMembers -= th
    members(ec) -= th
    if dets.get(ec).contains(th) then
      dets -= ec

  // TODO: to enhance
  def updateMemberDet(th: TH, ty: Type)(using ctx: Context): (Set[(Type, Type)], Set[(ECH, ECH)], Set[ECH]) =
    val ecOfTh = revMembers(th)
    dets.get(ecOfTh) match
      case Some(detTh) if detTh != th =>
        val detTy = storedTypes(detTh)
        val cstrts = Set((detTy, ty), (ty, detTy))
        removeMember(th)
        (cstrts, Set.empty, Set.empty)
      case _ =>
        // TODO: Can do better (see report)
        updateMember(th, ty)
        (Set.empty, Set.empty, Set.empty)

  def updateMember(th: TH, ty: Type): Unit =
    storedTypes.update(th, ty)

  def symsInEC(ec: ECH): Set[Symbol] =
    symsEC.filter(_._2 == ec).map(_._1).toSet

  //////////////////////////////////////////////////////////////////////

  def occursInHead(sym: Symbol, t: Type)(using Context): Boolean =
    t match
      case tr: TypeRef if tr == sym.typeRef => true
      case hk: HKTypeLambda => occursInHead(sym, hk.resType)
      case t: AndOrType => occursInHead(sym, t.tp1) || occursInHead(sym, t.tp2)
      case AppliedType(tycon, _) => occursInHead(sym, tycon)
      case _ => false

  def boundsForSym(sym: Symbol, full: Boolean)(using Context): TypeBounds =
    val ec = findECForSym(sym) match
      case Some((ec, _)) => ec
      case None =>
        return null

    dets.get(ec).map { detTH =>
      val res = externalizeType(storedTypes(detTH), Map.empty)
      TypeAlias(res)
    }.getOrElse {
      // TODO: Not stable!!!!
      // TODO: Not stable!!!!
      // TODO: Not stable!!!!
//      val arbitraryRepr = syms.last
//      if arbitraryRepr != sym then
//        TypeAlias(arbitraryRepr.typeRef)
//      else
      def externalizeAndFilter(t: Type): Option[Type] =
        // TODO: We don't need to this shenanigens if externalizeType pick the "representative symbol" correctly
        val ext = externalizeType(t, Map.empty)
        val ok = symsEC.forall {
          case (otherSym, otherEC) =>
            if otherEC == ec then
              !occursInHead(otherSym, ext)
            else
              full || !occursInHead(otherSym, ext)
//            if otherEC == ec then
//              ext != otherSym.typeRef
//            else
//              full || !occursInHead(otherSym, ext)
//            (ext != sym.typeRef) && (full || !occursInHead(otherSym, ext))
        }
        if ok then Some(ext)
        else None

      val (los, his) = bounds(ec, inclusive = true)
      val extLos = los.flatMap(externalizeAndFilter)
      val extHis = his.flatMap(externalizeAndFilter)

      // TODO: If full = true, could use & and | ?
      val combinedLo = extLos.reduceLeftOption(OrType.makeHk)
        .getOrElse(defn.NothingType)
      val combinedHi = extHis.reduceLeftOption(AndType.makeHk)
        .getOrElse(topOfKind(typeVarReprs(ec)))

      if combinedLo == combinedHi then
        TypeAlias(combinedLo)
      else
        TypeBounds(combinedLo, combinedHi)
    }

  // TODO: Do the same for externalized bounds.
  // TODO: Bad name. Only internalized
  def bounds(ec0: ECH, inclusive: Boolean)(using Context): (Set[Type], Set[Type]) =
    val ec = unionFind.find(ec0)
    val loECs = gSub.strictLowerBounds(ec)
    val hiECs = gSub.strictUpperBounds(ec)

    // TODO: Argumenter que, comme on ne store pas de AsEC telle quelles dans les ECs, on n'a aucun risque "d'exclure" des "bonne" bounds
    def ensureNonCyclic(tp: Type, fromBelow: Boolean): Type =
      tp match
        case tp: AndOrType =>
          val r1 = ensureNonCyclic(tp.tp1, fromBelow)
          val r2 = ensureNonCyclic(tp.tp2, fromBelow)
          if (r1 eq tp.tp1) && (r2 eq tp.tp2) then tp
          else tp.match
            case tp: OrType =>
              TypeComparer.lub(r1, r2, isSoft = tp.isSoft)
            case _ =>
              r1 & r2
        // TODO: Et les symbols ?
        // TODO: Et AppliedEC ?
        case AsEC(otherEC) =>
          // TODO: Check if we got this right
          if otherEC == ec
            || (!fromBelow && loECs.contains(otherEC))
            || (fromBelow && hiECs.contains(otherEC)) then
            if fromBelow then defn.NothingType
            else topOfKind(tp)
          else
            tp
        case hk: HKTypeLambda =>
          val res = ensureNonCyclic(hk.resType, fromBelow)
          if res eq hk.resType then hk
          else hk.newLikeThis(hk.paramNames, hk.paramInfos, res)
        case _ =>
          val tp1 = tp.dealiasKeepAnnots
          if tp1 ne tp then
            val tp2 = ensureNonCyclic(tp1, fromBelow)
            if tp2 ne tp1 then tp2 else tp
          else tp

    // We explicitly filter out Nothing because it does not play nicely with HK
    // types when mixing them with OrType/AndType.makeHk.
    // For instance, the top of the HK type [X] =>> T is [X] =>> Any (same kind), but its bottom type is Nothing (different kind)
    // Since Nothing and [X] ==> T do not have the same kind, OrType/AndType.makeHk mixes them in a way that is unsuitable for us.
    // So we just filter it out. We do not need to do that for Any because it does not suffer from the same problem as Nothing.
    val loTys = loECs.flatMap { loEC =>
      dets.get(loEC).map(detTH => Set(storedTypes(detTH)))
        .getOrElse(members(loEC).map(storedTypes).toSet)
    }.filterNot(_.isNothingType)
    val hiTys = hiECs.flatMap { hiEC =>
      dets.get(hiEC).map(detTH => Set(storedTypes(detTH)))
        .getOrElse(members(hiEC).map(storedTypes).toSet)
    }

    // TODO: Do something if determined
    // All types belonging to that EC are going to appear as lower and upper bounds.
    val equalTypes =
      if inclusive then members(ec).map(storedTypes)
      else Set.empty

    val allLos = (equalTypes ++ loTys)
      .map(ensureNonCyclic(_, fromBelow = true)).toSet
    val allHis = (equalTypes ++ hiTys)
      .map(ensureNonCyclic(_, fromBelow = false)).toSet

    (allLos, allHis)


  // TODO: Bad name. Only internalized
  def strictLowerBounds(ec0: ECH): Set[Type] =
    val ec = unionFind.find(ec0)
    gSub.strictLowerBounds(ec).flatMap(loEC => members(loEC).map(storedTypes))

  // TODO: Bad name. Only internalized
  def strictUpperBounds(ec0: ECH): Set[Type] =
    val ec = unionFind.find(ec0)
    gSub.strictUpperBounds(ec).flatMap(hiEC => members(hiEC).map(storedTypes))

  //////////////////////////////////////////////////////////////////////

  // TODO: Explain why. Essentially for isSubtype checks while processing things
  def asConstraint(using Context): Constraint =
    // All representatives EC handles
    val orderedECs = members.keys.toVector

//    val allTyVars = members.keys.flatMap(allTyVarsOf).toSet
//    val extTyVars = allTyVars -- internalTyVars
//    if extTyVars.nonEmpty then
//      println(extTyVars.map(_.show).mkString(", "))

    val cstrt0 = revTypeVarReprs.keys.foldLeft(origCstrt) {
      case (cstrt, tv) =>
        cstrt.add(tv.origin.binder, List(tv))
    }
    val cstrt1 = members.keys.foldLeft(cstrt0) {
      case (cstrt, ec) =>
        if members(ec).size == 1 then
          cstrt.updateEntry(typeVarReprs(ec).origin, storedTypes(members(ec).head))
        else
          val entry0 = dets.get(ec).map(storedTypes)
            .getOrElse {
              val (los, his) = bounds(ec, inclusive = true)
              TypeBounds(
                los.reduceLeftOption(OrType.makeHk)
                  .getOrElse(defn.NothingType),
                his.reduceLeftOption(AndType.makeHk)
                  .getOrElse(topOfKind(typeVarReprs(ec)))
              )
            }
          val entry =  entry0 match
            case TypeBounds(lo, hi) if lo == hi => lo
            case otherwise => otherwise
          cstrt.updateEntry(typeVarReprs(ec).origin, entry)
    }
    // Setting non-representative type variable to be equal to the representative type variable of each EC.
    val cstrt2 = orderedECs.foldLeft(cstrt1) {
      case (cstrt, ec) =>
        val tvRepr = typeVarReprs(ec)
        val tvsNonRepr = allInternalTyVarsOf(ec).filter(_ != tvRepr)
        tvsNonRepr.foldLeft(cstrt) {
          case (c, tvNonRepr) =>
            c.updateEntry(tvNonRepr.origin, tvRepr)
        }
    }
    // TODO: What about lo??? <- not needed? will be handled "automatically" as we traverse all edges?
    val cstrt3 = gSub.edges.foldLeft(cstrt2) {
      case (cstrt, (ec, hiECs)) =>
        hiECs.foldLeft(cstrt) {
          case (c, hiEC) =>
            c.addLess(typeVarReprs(ec).origin, typeVarReprs(hiEC).origin)
        }
    }
    cstrt3

  // Note: all ECs repr. are present, but some may have an empty Set of external tyvars.
  def externalTyVarsOfEC(ec0: ECH)(using ctx: Context): Set[TypeVar] =
    val ec = unionFind.find(ec0)
    allInternalTyVarsOf(ec).flatMap(int2ext.get)

  def externalizeEC(ec0: ECH, pending: Map[ECH, RecType])(using ctx: Context): Type =
    val ec = unionFind.find(ec0)
    val res = dets.get(ec).map(detTH => externalizeType(storedTypes(detTH), pending))
      .orElse(externalTyVarsOfEC(ec).headOption)
      // TODO: Externalize with symbols as well? Note that this can interfere with boundsForSym...
      // TODO: Pick the "represnentative symbol"
      .orElse(symsEC.find((_, cand) => cand == ec).map(_._1.typeRef))
      .orElse(
        // TODO: This is quite fragile. Find another way of doing that!!!!
        members(ec).map(storedTypes).find {
          case _: NamedType => true
          case _ => false
        })
      // TODO: This is quite fragile. Find another way of doing that!!!!
      .getOrElse {
        externalizeType(storedTypes(members(ec).head), pending)
      }
    res

  def externalizeType(ty: Type, pending: Map[ECH, RecType])(using Context): Type =
    val tm = new TypeMap {
      override def apply(tp: Type): Type = tp match
        case AsEC(otherEC) =>
          // TODO: If we appear in an injective position and that we have a cycle, occur checks fails, so the GADT pattern is unreachable.
          //  This would be an interesting improvement.
          // TODO: This is very hacky... and does not seem to do what is intended???
          // TODO: Prefer an approximation by lower/upper bound if we cannot externalize this thing
          val pend = pending.get(otherEC).map(t => LazyRef.of(t))
          pend.getOrElse {
            // TODO: Correct use of RecType??? Because we may have multiple RecTypes for the same EC!!!
            val res = RecType.closeOver(rec => {
              val ext = externalizeEC(otherEC, pending + (otherEC -> rec))
              ext
            })
            res
          }
        case _ =>
          mapOver(tp)
    }
    tm(ty)

  // TODO: Explain.
  // TODO: Externalize with symbols as well?
  def asExternalizedConstraint(using ctx: Context): Constraint =
    // All representatives EC handles
    val orderedECs = members.keys.toVector
    // Note: all ECs repr. are present, but some may have an empty Set of external tyvars.
    val allExtTyVarsOfECs = members.keys.map(ec => ec -> allInternalTyVarsOf(ec).flatMap(int2ext.get)).toMap

    // TODO: Explain
    def computeEntryForEC(ec: ECH): Type =
      val extTyVars = allExtTyVarsOfECs(ec)
      val entry0 = dets.get(ec)
        .map(detTH => externalizeType(storedTypes(detTH), Map.empty))
        .getOrElse {
          val (los, his) = bounds(ec, inclusive = true)
          // We exclude all external type vars for the visited EC appearing individually in lo/hi to avoid cycles
          // We could also say inclusive = false, but we may miss some other useful information
          TypeBounds(
            los.map(externalizeType(_, Map.empty))
              .filter {
                case tv: TypeVar => !extTyVars.contains(tv)
                case _ => true
              }
              .reduceLeftOption(OrType.makeHk)
              .getOrElse(defn.NothingType),
            his.map(externalizeType(_, Map.empty))
              .filter {
                case tv: TypeVar => !extTyVars.contains(tv)
                case _ => true
              }
              .reduceLeftOption(AndType.makeHk)
              .getOrElse(topOfKind(typeVarReprs(ec)))
          )
        }
      entry0 match
        case TypeBounds(lo, hi) if lo == hi => lo
        case otherwise => otherwise

    // ---------------------------------

    // TODO: "origCstrt": bad idea, things may change in between !!!
    val curr = ctx.typerState.constraint.asInstanceOf[OrderingConstraint]
    val cstrt0 = allExtTyVarsOfECs.values.flatten.foldLeft(curr) {
      case (cstrt, tv) =>
        // TODO: Sort things out with instantiated tyvars: basically, if we don't filter them out,
        //    we have problems with constraint state not being empty at the end of typer...
        // TODO: It seems that this step is unnecessary because curr should contain all ext. TVs ?
        if cstrt.contains(tv.origin.binder) || tv.isInstantiated then
          cstrt
        else
          cstrt.add(tv.origin.binder, List(tv))
    }

    val cstrt1 = members.keys.foldLeft(cstrt0) {
      case (cstrt, ec) =>
        // TODO: Sort things out with instantiated tyvars: basically, if we don't filter them out,
        //    we have problems with constraint state not being empty at the end of typer...
        val extTyVars = allExtTyVarsOfECs(ec).filterNot(_.isInstantiated)
        if extTyVars.isEmpty then
          // This EC does not have an associated external type variable, as such, we cannot represent it.
          cstrt
        else
          val entry = computeEntryForEC(ec)
          val (pickedAsRepr, others) = (extTyVars.head, extTyVars.tail)
          val updCstrt = cstrt.updateEntry(pickedAsRepr.origin, entry)
          others.foldLeft(updCstrt) {
            case (cstrt, tyVar) =>
              cstrt.updateEntry(tyVar.origin, pickedAsRepr)
          }
    }
    // TODO: is gSub.edges OK or should we explicitly order all tyvars?
    // TODO: is gSub.edges OK or should we explicitly order all tyvars?
    // TODO: is gSub.edges OK or should we explicitly order all tyvars?
    val cstrt2 = gSub.edges.foldLeft(cstrt1) {
      case (cstrt, (ec, hiECs)) =>
        allExtTyVarsOfECs(ec)
          .flatMap(ty => hiECs.flatMap(hiEC => allExtTyVarsOfECs(ec)).map(hiECTyVar => (ty, hiECTyVar)))
          .foldLeft(cstrt) {
            case (cstrt, (tyVar, hiTyVarEC)) =>
              cstrt.addLess(tyVar.origin, hiTyVarEC.origin)
          }
    }
    cstrt2

  def constraintPatternType(pat: Type, scrut: Type)(using ctx: Context): Boolean =
    // TODO: Not pretty...
    if pat.isErroneous || scrut.isErroneous then
      return false
    val derivedCstrts = createConstraints(pat, scrut) match
      case Some(cstrts) => cstrts
      case None => return false
    origCstrt = ctx.typerState.constraint.asInstanceOf[OrderingConstraint]
    val cstrts = derivedCstrts ++ breakConstraint(origCstrt)
    println(i"Constraint for $scrut matches $pat:")
    println("  " ++ cstrts.map((s, t) => i"$s <: $t").mkString(", "))
    val res = simplifyLoop(cstrts)
    res

  def findECForSym(sym: Symbol)(using ctx: Context): Option[(ECH, TypeVar)] =
    symsEC.get(sym).map(ec => (ec, typeVarReprs(ec)))

  def findOrCreateECForSym(sym: Symbol)(using ctx: Context): (ECH, TypeVar) =
    symsEC.get(sym) match
      case Some(ec) => (ec, typeVarReprs(ec))
      case None =>
        val (ec, tyVar) = findOrCreateEC(sym.denot.typeRef)
        symsEC += sym -> ec
        (ec, tyVar)

  def addSymbols(syms: List[Symbol])(using Context): Boolean =
    println(i"KNOWLEDGE: ADD ${syms.map(s => i"$s >: ${s.info.bounds.lo} <: ${s.info.bounds.hi}").mkString(", ")}")
//    println(debugString)
    val (ecs, tvars) = syms.map(findOrCreateECForSym).unzip

    val res = syms.zip(tvars).forall {
      case (sym, symTyVar) =>
        val tb = sym.info.bounds
        // TODO: Not pretty...
        if tb.isErroneous then
          false
        else
          val lo = tb.lo.subst(syms, tvars)
          val hi = tb.hi.subst(syms, tvars)
          simplifyLoop(Set((lo, symTyVar), (symTyVar, hi)))
    }
//    println(s"ADDED THE SYMBOLS: $res")
//    println(debugString)
//    println("======================")
    res

  def addBound(sym: Symbol, bound: Type, isUpper: Boolean)(using Context): Boolean =
    println(i"ADDING BOUNDS for $sym ${if isUpper then "<:" else ">:"} $bound")
//    println(debugString)
//    println(asExternalizedConstraint.show)
    val (symEC, symTyVar) = findOrCreateECForSym(sym)
    // TODO: Say why not EC-izing bound: because we can have sym <: T1 & T2, so its simpler to break that into sym <: T1, sym <: T2
    // val (boundEC, boundTyVar) = TFindOrCreateEC(bound)
    val res = simplifyLoop(
      if isUpper then Set((symTyVar, bound))
      else Set((bound, symTyVar)))
//    println(s"NOW WE HAVE (result is $res)")
//    println(debugString)
//    println(asExternalizedConstraint.show)
//    println("======================")
    res

  def isLess(lhs: Symbol, rhs: Symbol)(using Context): Boolean =
    findECForSym(lhs).zip(findECForSym(rhs)).map {
      case ((lhsEC, _), (rhsEC, _)) =>
        lhsEC == rhsEC || gSub.chain(lhsEC, rhsEC).isDefined
    }.getOrElse(false)

  def isABound(tr: NamedType, bound: Type, upper: Boolean)(using Context): Boolean =
    val trInt = internalize(tr, create = false)
    val boundInt = internalize(bound, create = false)
    trInt.zip(boundInt).map {
      case (AsEC(trEC), AsEC(boundEC)) =>
        trEC == boundEC
          || (upper && gSub.chain(trEC, boundEC).isDefined)
          || (!upper && gSub.chain(boundEC, trEC).isDefined)
      case (tr, bound) =>
        (upper && TECIsSubtype(tr, bound))
        || (!upper && TECIsSubtype(bound, tr))
    }.getOrElse(false)

  def instantiatedTVar(tvar: TypeVar, inst: Type)(using Context): Unit =
    val (_, internalTvar) = findOrCreateEC(tvar)
    val (_, instTvar) = findOrCreateEC(inst)
    simplifyLoop(Set((internalTvar, instTvar), (instTvar, internalTvar)))

  def simplifyLoop(cstrts: Set[(Type, Type)])(using Context): Boolean =
    val cstrtsStack = mutable.Stack.from(cstrts)
    while cstrtsStack.nonEmpty do
      val (s, t) = cstrtsStack.pop()
//      println(i"DEDUCTION FOR $s <: $t")
      deductionIneq(s, t) match
        case Some(deductions) =>
//          println("--> We have: " + deductions.map((a, b) => i"$a <: $b").mkString(", "))
//          println("---------------------\n")
          val newCsrtrts = deductions.foldLeft(Set.empty[(Type, Type)]) {
            case (acc, (u, v)) => acc ++ compact(u, v)
          }
          cstrtsStack ++= newCsrtrts
        case None => return false
    true

  def mergeLoop(toMerge: Set[(ECH, ECH)])(using Context): Set[(Type, Type)] =
    val cstrts = mutable.Set.empty[(Type, Type)]
    val toMergeStack = mutable.Stack.from(toMerge)
    while toMergeStack.nonEmpty do
      val (a, b) = toMergeStack.pop()
      val aa = unionFind.find(a)
      val bb = unionFind.find(b)
      if aa != bb then
        val (newCsrts, newToMerge) = merge(aa, bb)
        cstrts ++= newCsrts
        toMergeStack ++= newToMerge
    cstrts.toSet

  def breakConstraint(cstrt: Constraint)(using ctx: Context): Set[(Type, Type)] =
    val res = (for
      // TODO: What should we do for TypeParamRefs that are not associated to a TypeVar?
      tyParamRef <- cstrt.domainParams
      tyVar = cstrt.typeVarOfParam(tyParamRef)
      if tyVar.exists
      loTyVars = cstrt.lower(tyParamRef).map(cstrt.typeVarOfParam).filter(_.exists)
      hiTyVars = cstrt.upper(tyParamRef).map(cstrt.typeVarOfParam).filter(_.exists)
      nonParam = cstrt.nonParamBounds(tyParamRef)
      res <- loTyVars.map(lo => (lo, tyVar)) ++ hiTyVars.map(hi => (tyVar, hi))
        ++ List((nonParam.lo, tyVar), (tyVar, nonParam.hi))
    yield res).toSet
//    println("Breaking:")
//    println(cstrt.show)
//    println("into:")
//    println(res.map((s, t) => i"$s <: $t").mkString(", "))
//    println("----------")
    res

  // TODO: this fn incorporates a weak form of deductionPathTyped
  def createConstraints(pat0: Type, scrut0: Type)(using ctx: Context): Option[Set[(Type, Type)]] =
    def invariantIntersection(variances: List[Variance], argsL: List[Type], argsR: List[Type]): Set[(Type, Type)] =
      assert(variances.size == argsL.size)
      assert(argsL.size == argsR.size)
      variances.zip(argsL.zip(argsR)).foldLeft(Set.empty[(Type, Type)]) {
        case (acc, (v, (argL, argR))) if varianceToInt(v) == 0 =>
          acc ++ Set((argL, argR), (argR, argL))
        case (acc, _) => acc
      }

    def relatedClassesIntersection(clsL: ClassSymbol, argsL: List[Type], clsR: ClassSymbol, argsR: List[Type]): Set[(Type, Type)] =
      assert(clsL.classDenot.derivesFrom(clsR))
      // Variance of the right-hand side class, not the left
      val variances = clsR.typeParams.map(_.paramVariance)
      val (leftUpcasted, boundsCstrts) = upcastTo(clsL, argsL, clsR)
      leftUpcasted.foldLeft(boundsCstrts) {
        case (acc, AppliedType(_, argsL)) =>
          acc ++ invariantIntersection(variances, argsL, argsR)
        case (acc, _) => acc
      }

    def eliminateImpossibleInhabitation(dnf: Set[Set[Type]]): Set[Set[Type]] =
      def provablyNotInhabited(conj: Set[Type]): Boolean =
        unordPairs(conj).exists {
          case (AsClassOrTrait(s, _), AsClassOrTrait(t, _)) =>
            val unrelated = !s.derivesFrom(t) && !t.derivesFrom(s)
            val sIsTrait = s.is(Trait)
            val tIsTrait = t.is(Trait)
            val classIntersection = !s.is(Trait) && !t.is(Trait) && unrelated
            val sFinal = (s.is(Final) || s.is(Case)) && unrelated
            val tFinal = (t.is(Final) || t.is(Case)) && unrelated
            classIntersection || sFinal || tFinal
          case _ => false
        }
      dnf.filterNot(provablyNotInhabited)

    // TODO: Meh for term ref!!! We don't want to lose them!!!
    // TODO: Suboptimal
    // TODO: Disgusting
    def stripTermRefAndExprType(t: Type): Type = t match
      case tr: TermRef => stripTermRefAndExprType(tr.denot.info)
      case exp: ExprType => stripTermRefAndExprType(exp.resType)
      case t => t

    // TODO: Suboptimal
    // TODO: Disgusting, absolutuely fragile
    // TODO: For refinedtype, we can do better, provided that we have a val x: RefinedType
    def stripRefinement(tp: Type): Type = tp match {
      case tp: RefinedOrRecType => stripRefinement(tp.parent)
      case tp => tp
    }

    // TODO: If we have an & in scrut, and/or an | in pat, could we break that into 2 recursive calls?

    ////////////////////////////////////////////////

    val pat0Dealias = stripRefinement(pat0.dealias)
    val scrut0Dealias = stripRefinement(scrut0.dealias)

    // If the pattern is a final class, we can generate even stronger constraints pat <: scrut \/ scrut <: pat

    val moreConstraints: Set[(Type, Type)] = {
      val more = pat0Dealias match
        case AsClassOrTrait(cls, _) =>
          cls.is(Final) || cls.is(Case)
        // TODO: Does this properly cover object within enum and "object module"?
        case tr: TermRef =>
          tr.symbol.is(CaseVal) || tr.symbol.is(Final)
        case _ => false
      if more then
        // TODO: argue why we have pat <: scrut *or* scrut <: pat, and why we can generate stronger constraint (maybe put that above)
        val l = deductionIneq(pat0Dealias, scrut0Dealias)
        val r = deductionIneq(scrut0Dealias, pat0Dealias)
        approxDisj(l, r) match
          case Some(cstrts) => cstrts
          case None => return None // Contradiction found, we early-exit this function
      else Set.empty
    }

    // TODO: dealias + strip ok?
    // TODO: What if we have something like TermRef & TermRef for pat or scrut ???
    // TODO: This is really messy, we should have a thing dedicated to term constraints
    val pat = stripTermRefAndExprType(pat0Dealias)
    val scrut = stripTermRefAndExprType(scrut0Dealias)

    val intersectDNF = disjunctions(pat & scrut)
    val intersectDNF2 = eliminateImpossibleInhabitation(intersectDNF)
    val inCommon = commonTypes(intersectDNF2)
    val pairs = inCommon.flatMap(a => inCommon.flatMap(b => if a == b then None else Some((a, b))))
    Some(pairs.foldLeft(moreConstraints) {
      case (acc, (AsClassOrTrait(clsL, argsL), AsClassOrTrait(clsR, argsR))) =>
        // Note: subsumes the case where clsL == clsR
        if clsL.classDenot.derivesFrom(clsR) then
          acc ++ relatedClassesIntersection(clsL, argsL, clsR, argsR)
        else
          // TODO: Comments + make sure it's correct...
          val rhsParents = clsR.classDenot.classInfo.parents
          val rhsUpcastsInit = Set.empty[(ClassSymbol, List[Type])]
          val boundsCstrtsInit = Set.empty[(Type, Type)]
          val (rhsUpcasts, boundsCstrts) = rhsParents.foldLeft((rhsUpcastsInit, boundsCstrtsInit)) {
            case ((rhsUpcastsAcc, boundsCstrtsAcc), AsClassOrTrait(rhsParent, _)) if clsL.derivesFrom(rhsParent) =>
              val (rhsUpcasts0, boundsCstrts) = upcastTo(clsR, argsR, rhsParent)
              val rhsUpcasts = rhsUpcasts0.collect {
                case AsClassOrTrait(commonParent, commonParentArgs) => ((commonParent, commonParentArgs))
              }
              (rhsUpcastsAcc ++ rhsUpcasts, boundsCstrtsAcc ++ boundsCstrts)
            case (acc, _) => acc
          }
          val intersectionCstrts =
            rhsUpcasts.flatMap((commonParent, commonParentArgs) =>
              relatedClassesIntersection(clsL, argsL, commonParent, commonParentArgs))
          acc ++ boundsCstrts ++ intersectionCstrts

      case (acc, (AppliedType(tyconL: TypeRef, argsL), AppliedType(tyconR: TypeRef, argsR))) =>
        acc ++ constraintsFromTyconBounds(tyconL, argsL) ++ constraintsFromTyconBounds(tyconR, argsR)

      case (acc, (AppliedType(tyconL: TypeRef, argsL), _)) =>
        acc ++ constraintsFromTyconBounds(tyconL, argsL)

      case (acc, (_, AppliedType(tyconR: TypeRef, argsR))) =>
        acc ++ constraintsFromTyconBounds(tyconR, argsR)

      case (acc, _) => acc
    })


  // TODO: For HK Type, we absolutely need to replace the binder in one of the the members to ensure that we get the most out of it
  def deductionIneq(s0: Type, t0: Type)(using ctx: Context): Option[Set[(Type, Type)]] =
    def stripExprType(t: Type): Type = t match
      case exp: ExprType => stripExprType(exp.resType)
      case t => t

    // TODO: Dealias ok?
    val s = etaExpandIfNeeded(stripExprType(s0.dealias))
    val t = etaExpandIfNeeded(stripExprType(t0.dealias))
    (s, t) match
      // TODO: Refinement things

      // TODO: Difference between isAny and isAnyRef?
      // TODO: Properly deal with this AnyKind thing
      case (s, t) if s.isNothingType || t.isAny || s == t || t.isAnyKind =>
        Some(Set.empty)

      // TODO: check this
      case (TypeBounds(lo, hi), t) =>
        deductionIneq(lo, t)
        // deductionIneq(lo, t).zip(deductionIneq(hi, t)).map((los, his) => los ++ his)

      case (s, TypeBounds(lo, hi)) =>
        deductionIneq(s, hi)
        // deductionIneq(s, lo).zip(deductionIneq(t, hi)).map((los, his) => los ++ his)

      case (AppliedType(tyconL: TypeRef, argsL), AppliedType(tyconR: TypeRef, argsR)) if tyconL.symbol.isClass && tyconR.symbol.isClass =>
        val clsL: ClassSymbol = tyconL.symbol.asClass
        val clsR: ClassSymbol = tyconR.symbol.asClass
        // TODO: Comp ok ?
        if clsL == clsR then
          val variances = clsL.typeParams.map(_.paramVariance)
          variances.zip(argsL.zip(argsR)).foldLeft(Option(Set.empty[(Type, Type)])) {
            case (Some(acc), (v, (argL, argR))) =>
              if v.is(Covariant) then
                deductionIneq(argL, argR).map(_ ++ acc)
              else if v.is(Contravariant) then
                deductionIneq(argR, argL).map(_ ++ acc)
              else
                deductionIneq(argL, argR).zip(deductionIneq(argR, argL))
                  .map((lr, rl) => lr ++ rl ++ acc)
            case (None, _) => None
          }
        else if clsL.classDenot.derivesFrom(clsR) then
          val (leftUpcasted, _) = upcastTo(clsL, argsL, clsR)
          deductionIneq(leftUpcasted.reduce(AndType.make(_, _, true)), t)
        else
          None

      case (AppliedType(tyconL: TypeRef, argsL), tyconR: TypeRef) if tyconL.symbol.isClass && tyconR.symbol.isClass =>
        val clsL: ClassSymbol = tyconL.symbol.asClass
        val clsR: ClassSymbol = tyconR.symbol.asClass

        // TODO: Comp ok ?
        if clsL == clsR then
        // TODO: This case is meaningless, right?
          Some(Set.empty)
        else if clsL.classDenot.derivesFrom(clsR) then
          val (leftUpcasted, _) = upcastTo(clsL, argsL, clsR)
          deductionIneq(leftUpcasted.reduce(AndType.make(_, _, true)), t)
        else
          None

      case (tyconL: TypeRef, AppliedType(tyconR: TypeRef, _)) if tyconL.symbol.isClass && tyconR.symbol.isClass =>
        val clsL: ClassSymbol = tyconL.symbol.asClass
        val clsR: ClassSymbol = tyconR.symbol.asClass

        // TODO: Comp ok ?
        if clsL == clsR then
        // TODO: This case is meaningless, right?
          Some(Set.empty)
        else if clsL.classDenot.derivesFrom(clsR) then
          val (leftUpcasted, _) = upcastTo(clsL, Nil, clsR)
          deductionIneq(leftUpcasted.reduce(AndType.make(_, _, true)), t)
        else
          None

      case (tyconL: TypeRef, tyconR: TypeRef) if tyconL.symbol.isClass && tyconR.symbol.isClass =>
        val clsL: ClassSymbol = tyconL.symbol.asClass
        val clsR: ClassSymbol = tyconR.symbol.asClass

        // TODO: Comp ok ?
        if clsL == clsR then
          Some(Set.empty)
        else if clsL.classDenot.derivesFrom(clsR) then
          val (leftUpcasted, _) = upcastTo(clsL, Nil, clsR)
          // TODO: reduce ~> foldLeft
          // TODO: or should we "never" encounter empty leftUpcasted ?
          deductionIneq(leftUpcasted.reduce(AndType.make(_, _, true)), t)
        else
          None

      case (AppliedType(tyconL: TypeRef, argsL), AppliedType(tyconR: TypeRef, argsR)) =>
        Some(Set((s, t)))

      // TODO: For these two remarks: we need to register bounds on EC creation
      case (s, t: AndType) =>
        // TODO: ++ Set((s, t)) to help a bit for equality like X & Y = Z & W
        deductionIneq(s, t.tp1).zip(deductionIneq(s, t.tp2)).map((a, b) => a ++ b ++ (if s.isInstanceOf[AndType] then Set((s, t)) else Set.empty))

      case (s: OrType, t) =>
        // TODO: ++ Set((s, t)) to help a bit for equality like X | Y = Z | W
        deductionIneq(s.tp1, t).zip(deductionIneq(s.tp2, t)).map((a, b) => a ++ b ++ (if t.isInstanceOf[OrType] then Set((s, t)) else Set.empty))

      case (s, t: OrType) =>
        approxDisj(deductionIneq(s, t.tp1), deductionIneq(s, t.tp2)).map(_ ++ Set((s, t)))

      case (s: AndType, t) =>
        approxDisj(deductionIneq(s.tp1, t), deductionIneq(s.tp2, t)).map(_ ++ Set((s, t)))

      case (s: TypeRef, t) if !s.hasSimpleKind =>
        deductionIneq(s.EtaExpand(s.typeParams), t)

      case (s, t: TypeRef) if !t.hasSimpleKind =>
        deductionIneq(s, t.EtaExpand(t.typeParams))

      case (sOld: HKTypeLambda, tOld: HKTypeLambda) =>
        // TODO: We do not have a "undet" to differentiate from "false -- not sure"
        val (s, t) = alphaRename(sOld, tOld)
        val sBounds = boundsInfoOf(s)
        val tBounds = boundsInfoOf(t)
        // TODO
        // TODO
        // TODO
        // TODO
        // TODO
        // FIXME
        // assert(sBounds.corresponds(tBounds) { case ((vl, tyParamL, _), (vr, tyParamR, _)) => vl == vr && tyParamL == tyParamR })
        // TODO: No, must substitute one of the hk body with one of the other binder
        val tyParams = sBounds.map(_._2)
        if !BSubsumes(tBounds, sBounds) then
          return Some(Set.empty)

        val boundsOfSEntailed = BEntailed(sBounds)
        def noOccurrenceOfTyVars(l: Type, r: Type): Boolean =
          tyParams.forall(tyParam => !tyParam.occursIn(l) && !tyParam.occursIn(r))

        deductionIneq(s.resType, t.resType) match
          case Some(res) =>
            Some(res.flatMap((l, r) =>
              if boundsOfSEntailed && noOccurrenceOfTyVars(l, r) then Some((l, r))
              else
                // We filter out useless results such as X0 <: X0
                // where X0 is a bound type parameter of s and t
                // Otherwise, we would get constraints such as [X0] =>> X0 <: [X0] ==> X0
                // While they are harmless, they pollute the structure.
                (l, r) match
                  case (l: TypeParamRef, r: TypeParamRef)
                  // TODO: Say l and r may be from t and s (swapped)
                  if ((l.binder eq s) || (l.binder eq t)) && ((r.binder eq s) || (r.binder eq t)) && l.paramNum == r.paramNum =>
                    None
                  case _ =>
                    Some((closeOver(l, sBounds), closeOver(r, tBounds)))
            ))
//          case Some(res) if boundsOfSEntailed && noOccurrenceOfTyVars(res) =>
//            Some(res)
//          case Some(res) =>
//            Some(res.map((l, r) => (closeOver(l, sBounds), closeOver(r, tBounds))))
          case None =>
            if boundsOfSEntailed then None
            else Some(Set.empty)

      case (s: TypeRef, t: TypeRef) if s.symbol.isClass && t.symbol.isClass && !s.symbol.asClass.classDenot.derivesFrom(t.symbol.asClass) =>
        None

      // TODO: Do the same for applied type ref
      case (s: TypeRef, t) if s.denot.info.isInstanceOf[TypeBounds] =>
        deductionIneq(s.denot.info, t).map(_ ++ Set((s, t)))

      case (s, t: TypeRef) if t.denot.info.isInstanceOf[TypeBounds] =>
        deductionIneq(s, t.denot.info).map(_ ++ Set((s, t)))

      // TODO: Explain this
      // TODO: Restrict to case object only: how to do that???
      case (s: TermRef, t) =>
        val tClassSym = t match
          case tr: TypeRef if tr.symbol.isClass =>
            tr.symbol.asClass
          case AppliedType(tr: TypeRef, _) if tr.symbol.isClass =>
            tr.symbol.asClass
          case _ => return Some(Set((s, t)))

        val sParents = fromAnds(s.denot.info)
        Some(sParents.foldLeft(Set((s, t)): Set[(Type, Type)]) {
          case (acc, parent: TypeRef) if parent.symbol.isClass =>
            // TODO: Is it sensical to use the bounds info?
            val (lubOfS, _) = upcastTo(parent.symbol.asClass, Nil, tClassSym)
            // TODO: Properly handle contradiction by returning None
            acc ++ lubOfS.flatMap(deductionIneq(_, t)).flatten
          case (acc, AppliedType(parentTycon: TypeRef, parentArgs)) if parentTycon.symbol.isClass =>
            // TODO: Is it sensical to use the bounds info?
            val (lubOfS, _) = upcastTo(parentTycon.symbol.asClass, parentArgs, tClassSym)
            // TODO: Properly handle contradiction by returning None
            acc ++ lubOfS.flatMap(deductionIneq(_, t)).flatten
          case (acc, _) => acc
        })

      case (s, t: TermRef) =>
//        println(i"B: $s <: $t")
        deductionIneq(s, t.denot.info).map(_ ++ Set((s, t)))

      // TODO: other cases to consider: in particular, things may break if we get RecType or other bizarre stuff
      case _ =>
//        println(i"Unmatched deduction: $s <: $t")
        Some(Set((s, t)))

//      case (s: TypeRef, t: TypeRef) => Some(Set((s, t)))
//
//      // TODO: other cases to consider
//      case _ => Some(Set.empty)

  def compact(s: Type, t: Type)(using ctx: Context): Set[(Type, Type)] =
//    val msg = i"COMPACT $s <: $t"
//    println(msg)
//    println(debugString)
    val (sEC, sTyVar) = findOrCreateEC(s)
//    println(i"EC for $s is [$sEC] (with tyvar $sTyVar)")
    val (tEC, tTyVar) = findOrCreateEC(t)
//    println(i"EC for $t is [$tEC] (with tyvar $tTyVar)")

    addIneq(sEC, tEC) match
      case Left(()) =>
        mergeLoop(Set((sEC, tEC)))
      case Right(cstrts) =>
        cstrts

  def addIneq(a: ECH, b: ECH)(using Context): Either[Unit, Set[(Type, Type)]] =
    if !gSub.chain(b, a).isEmpty then
      Left(())
    else if !gSub.chain(a, b).isEmpty then
      Right(Set.empty)
    else
      val newCstrts = ineqConstraints(a, b)
      gSub.addIneq(a, b)
      Right(newCstrts)

  // TODO: Name
  def ineqConstraints(a: ECH, b: ECH)(using Context): Set[(Type, Type)] =
    val strictLoWDets = gSub.strictLowerBounds(a).flatMap(weaklyDetsOf)
    val strictHiWDets = gSub.strictUpperBounds(b).flatMap(weaklyDetsOf)
    cartesian(strictLoWDets, strictHiWDets) ++
      cartesian(weaklyDetsOf(a), strictHiWDets) ++
      cartesian(strictLoWDets, weaklyDetsOf(b))

  def merge(a: ECH, b: ECH)(using Context): (Set[(Type, Type)], Set[(ECH, ECH)]) =
    def helper: (Set[(Type, Type)], Set[(ECH, ECH)]) =
      val ab = unionFind.union(a, b)

      val membsA = members(a).toSet
      val membsB = members(b).toSet
      members -= a
      members -= b
      members += ab -> mutable.Set.from(membsA ++ membsB)

      revMembers.mapValuesInPlace {
        case (_, ec) =>
          if ec == a || ec == b then ab
          else ec
      }
      symsEC.mapValuesInPlace {
        case (_, ec) =>
          if ec == a || ec == b then ab
          else ec
      }

      if dets.contains(a) then
        val detA = dets(a)
        dets -= a
        dets -= b
        dets += ab -> detA
      else if dets.contains(b) then
        val detB = dets(b)
        dets -= a
        dets -= b
        dets += ab -> detB

      val tyVarReprA = typeVarReprs(a)
      val tyVarReprB = typeVarReprs(b)
      if ab == a then
        typeVarReprs(b) = tyVarReprA
        revTypeVarReprs(tyVarReprB) = a
      else
        assert(ab == b)
        typeVarReprs(a) = tyVarReprB
        revTypeVarReprs(tyVarReprA) = b

      gSub.merge(a, b, ab)

      // TODO: Remove duplicate member using GEC (TBD) instead of brute-forcing
      val allMembs = allMembers
      // FIXME
      val toBeRm = members.values.flatMap(
        // Members within a same EC becoming equivalent
        ths => unordPairs(ths.toSet).filterNot((th1, th2) =>
          TECEquiv(storedTypes(th1), storedTypes(th2))).toSet)
      //      toBeRm.foreach((th1, _) => removeMember(th1))

      // TODO: Find equivalent classes using GEC (TBD) instead of brute-forcing
      val ecsUnordPairs = unordPairs(members.keys.toSet)
      val toMerge = ecsUnordPairs.flatMap { case (ec1, ec2) =>
        val ths1 = members(ec1)
        val ths2 = members(ec2)
        val thsPairs = ths1.flatMap(th1 => ths2.map(th2 => (th1, th2)))
        thsPairs.find((th1, th2) => TECEquiv(storedTypes(th1), storedTypes(th2)))
          .map(_ => (ec1, ec2))
      }

      val lowerWDets = gSub.strictLowerBounds(ab).flatMap(weaklyDetsOf)
      val upperWDets = gSub.strictUpperBounds(ab).flatMap(weaklyDetsOf)
      val cstrts = lowerWDets.flatMap(l => upperWDets.map(r => (l, r)))
      (cstrts, toMerge)

    ///////////////////////////////////////

//    println(s"MERGING $a WITH $b")
//    println(debugString)

    val allCsrts = mutable.Set.empty[(Type, Type)]
    val allToMerge = mutable.Set.empty[(ECH, ECH)]

    gSub.chain(a, b) match
      case Some(chain) if chain.length == 2 =>
        assert(chain == Seq(a, b))
        allCsrts ++= ineqConstraints(b, a)
      case Some(chain) =>
        return (Set.empty, chain.zip(chain.tail).toSet)
      case None =>
        gSub.chain(b, a) match
          case Some(chain) if chain.length == 2 =>
            assert(chain == Seq(b, a))
            allCsrts ++= ineqConstraints(a, b)
          case Some(chain) =>
            return (Set.empty, chain.zip(chain.tail).toSet)
          case None =>
            allCsrts ++= ineqConstraints(a, b)
            allCsrts ++= ineqConstraints(b, a)
            gSub.addIneq(a, b)

    (dets.contains(a), dets.contains(b)) match
      case (true, true) =>
        allCsrts += storedTypes(dets(a)) -> storedTypes(dets(b))
        allCsrts += storedTypes(dets(b)) -> storedTypes(dets(a))
        removeMember(dets(a))
      case (true, false) =>
        val (cstrts, toMerge) = propagateDeterminacy(b, storedTypes(dets(a)))
        allCsrts ++= cstrts
        allToMerge ++= toMerge
        if dets.contains(b) then
          allCsrts += storedTypes(dets(a)) -> storedTypes(dets(b))
          allCsrts += storedTypes(dets(b)) -> storedTypes(dets(a))
          removeMember(dets(b))
      case (false, true) =>
        val (cstrts, toMerge) = propagateDeterminacy(a, storedTypes(dets(b)))
        allCsrts ++= cstrts
        allToMerge ++= toMerge
        if dets.contains(a) then
          allCsrts += storedTypes(dets(a)) -> storedTypes(dets(b))
          allCsrts += storedTypes(dets(b)) -> storedTypes(dets(a))
          removeMember(dets(a))
      case (false, false) =>
        ()

//    println("ALL CSTRTS: " + allCsrts.map((s, t) => i"$s <: $t"))
    val (cstrts, toMerge) = helper
    allCsrts ++= cstrts
    allToMerge ++= toMerge
//    println("MERGE FINISHED:")
//    println(debugString)
//    println("NEW CSTRST: "+allCsrts.map((s, t) => i"$s <: $t").mkString(", "))
//    println("NEW TO MERGE: "+toMerge)
    (allCsrts.toSet, allToMerge.toSet)

  // TODO: to enhance
  def propagateDeterminacy(ec: ECH, detType: Type)(using Context): (Set[(Type, Type)], Set[(ECH, ECH)]) =
    def gatherAffected(ec: ECH, det: Type, processed: Set[ECH]): (Set[TH], Set[TH], Set[ECH]) =
      //      if processed.contains(ec) then
      //        return (Set.empty, Set.empty, Set.empty)
      // TODO: Use GEC (TBD) instead of brute-forcing
      val allMembs = allMembers
      val dnfs = allMembs.filter(th => storedTypes(th).isInstanceOf[AndOrType])
      (allMembs, dnfs, Set.empty)

    def gatherPotentiallyAffected: Map[TH, Set[Type]] =
      // TODO: We only get abstract type constructors ? What about HK TypeVar ?
      def abstractTyCon(th: TH): Option[TypeRef] = storedTypes(th) match
        case AppliedType(f: TypeRef, _) if !f.symbol.isClass =>
          Some(f)
        case HKTypeLambda(_, AppliedType(f: TypeRef, _)) if !f.symbol.isClass =>
          Some(f)
        case _ =>
          None

      members(ec).foldLeft(Map.empty[TH, Set[Type]]) {
        case (acc, ecTh) =>
          abstractTyCon(ecTh) match
            case Some(f) =>
              // TODO: Use GSym (TBD) instead of brute-forcing
              val candidateThs: Set[TH] = members.filter((otherEC, _) => otherEC != ec)
                .values.flatten.toSet
                .flatMap(th => abstractTyCon(th).filter(_ == f).map(_ => th))
              val added = candidateThs.map(candTh => candTh -> Set(storedTypes(ecTh))).toMap
              (acc.keySet ++ added.keySet)
                .map(k => k -> (acc.getOrElse(k, Set.empty) ++ added.getOrElse(k, Set.empty))).toMap
            case None =>
              acc
      }

    // TODO
    def propagateHeadSubst(headSubst: Set[TH]): (Set[(Type, Type)], Set[(ECH, ECH)], Set[ECH]) =
      headSubst.foldLeft((Set.empty[(Type, Type)], Set.empty[(ECH, ECH)], Set.empty[ECH])){
        case ((accCstrts, accToMerge, accDets), h) =>
          storedTypes(h) match
            case dnf: AndOrType =>
              val s = applyHeadSubst(dnf, ec, detType)
              // TODO: Simplify dnf
              s match
                // TODO: Missing case
                //                case otherEc: ECType =>
                //                  // TODO
                //                  ???
                case s if isDet(s) =>
                  val (cstrts, toMerge, dets) = updateMemberDet(h, s)
                  (accCstrts ++ cstrts, accToMerge ++ toMerge, accDets ++ dets)
                case s =>
                  updateMember(h, s)
                  (accCstrts, accToMerge, accDets)
            case t =>
              val s = applyHeadSubst(t, ec, detType)
              if isDet(s) then
                val (cstrts, toMerge, dets) = updateMemberDet(h, s)
                (accCstrts ++ cstrts, accToMerge ++ toMerge, accDets ++ dets)
              else
                updateMember(h, s)
                (accCstrts, accToMerge, accDets)
      }

    // TODO
    def propagateDNFRefresh(dnfRefresh: Set[TH]): (Set[(Type, Type)], Set[(ECH, ECH)], Set[ECH]) =
      dnfRefresh.foldLeft((Set.empty[(Type, Type)], Set.empty[(ECH, ECH)], Set.empty[ECH])){
        case ((accCstrts, accToMerge, accDets), h) =>
          val dnf = storedTypes(h) // .asInstanceOf[DNF] // TODO: commented for otherEc: ECType pattern to not flag as unreachable
          // TODO: Simplify dnf
          val s = dnf
          s match
            // TODO: Missing case
            //            case otherEc: ECType =>
            //              // TODO
            //              ???
            case s if isDet(s) =>
              val (cstrts, toMerge, dets) = updateMemberDet(h, s)
              (accCstrts ++ cstrts, accToMerge ++ toMerge, accDets ++ dets)
            case s =>
              updateMember(h, s)
              (accCstrts, accToMerge, accDets)
      }

    def propagateTrySubst(trySubst: Map[TH, Set[Type]]): (Set[(Type, Type)], Set[(ECH, ECH)], Set[ECH]) =
      trySubst.foldLeft((Set.empty[(Type, Type)], Set.empty[(ECH, ECH)], Set.empty[ECH])) {
        case ((accCstrts, accToMerge, accDets), (h, cands)) =>
          cands.foldLeft((accCstrts, accToMerge, accDets)) {
            case ((accCstrts, accToMerge, accDets), cand) =>
              tryApplyHeadSubst(storedTypes(h), cand, detType) match
                case Some(s) if isDet(s) =>
                  val (cstrts, toMerge, dets) = updateMemberDet(h, s)
                  (accCstrts ++ cstrts, accToMerge ++ toMerge, accDets ++ dets)
                case _ =>
                  (accCstrts, accToMerge, accDets)
          }
      }

    val (headSubst, refreshDNF, _) = gatherAffected(ec, detType, Set.empty)
    val trySubst = gatherPotentiallyAffected
    val (cstrts1, toMerge1, dets1) = propagateHeadSubst(headSubst)
    val (cstrts2, toMerge2, dets2) = propagateDNFRefresh(refreshDNF -- headSubst)
    val (cstrts3, toMerge3, dets3) = propagateTrySubst(trySubst)

    (dets1 ++ dets2 ++ dets3)
      .foldLeft((cstrts1 ++ cstrts2 ++ cstrts3, toMerge1 ++ toMerge2 ++ toMerge3)) {
        case ((accCstrts, accToMerge), detEC) =>
          val (cstrts, toMerge) = propagateDeterminacy(detEC, storedTypes(dets(detEC)))
          (accCstrts ++ cstrts, accToMerge ++ toMerge)
      }

  //////////////////////////////////////////////////////////////////////

  def applyHeadSubst(target: Type, ec: ECH, to: Type)(using Context): Type =
    target match
      //      case t: AndOrType => applyHeadSubst(toDNF(t), ec, to)
      case AsEC(otherEC) if unionFind.find(otherEC) == unionFind.find(ec) =>
        to
      case AsAppliedEC(otherEC, args) if unionFind.find(otherEC) == unionFind.find(ec) =>
        assert(to.isInstanceOf[HKTypeLambda])
        val hk = to.asInstanceOf[HKTypeLambda]
        assert(hk.paramRefs.corresponds(args)((l, r) => l.hasSameKindAs(r)))
        hk.appliedTo(args)
      case t: AndOrType =>
        toDNF(disjunctions(t).map(conjs => conjs.map(applyHeadSubst(_, ec, to)).reduce(AndType.make(_, _, true)))
          .reduce(OrType.make(_, _, false))) // TODO: Soft = ???
      //        val disjsSubst = mutable.Set.empty[Set[Type]]
      //        for (disjs <- disjunctions) {
      //          val conjsSubst = mutable.Set.empty[Type]
      //          for (conj <- disjs) {
      //            conjsSubst += applyHeadSubst(conj, ec, to)
      //          }
      //          disjsSubst += conjsSubst.toSet
      //        }
      //        toDNF(disjsSubst.toSet)
      case hk: HKTypeLambda =>
        hk.newLikeThis(hk.paramNames, hk.paramInfos, applyHeadSubst(hk.resType, ec, to))
      case t => t

  // TODO: eta-exp etc.
  def tryApplyHeadSubst(target: Type, from: Type, to: Type)(using Context): Option[Type] =
    assert(from.hasSameKindAs(to))
    (target, from) match
      case (AppliedType(tycon1: TypeRef, args1), AppliedType(tycon2: TypeRef, args2))
        if tycon1 == tycon2 && args1.corresponds(args2)((a1, a2) => TECEquiv(a1, a2)) =>
        Some(to)

      case (hk1@HKTypeLambda(_, AppliedType(tycon1: TypeRef, _)),
      hk2@HKTypeLambda(_, AppliedType(tycon2: TypeRef, _)))
        if tycon1 == tycon2 =>
        // TODO: No, must substitute one of the hk body with one of the other binder
        val (hk2Renamed, toRenamed) = alphaRename(hk2, to.asInstanceOf[HKTypeLambda])
        assert(hk2Renamed.paramRefs == toRenamed.paramRefs)

        TECTryMatch(hk2Renamed.paramRefs.toSet, hk2Renamed.resType, hk1.resType).map {
          subst =>
            // TODO: correct use of substParams?
            val toBodySubsted = toRenamed.resType.substParams(toRenamed, orderedSubst(toRenamed.paramRefs, subst))
            hk1.newLikeThis(hk1.paramNames, hk1.paramInfos, toBodySubsted)
        }

      case (AppliedType(tycon1: TypeRef, args1),
      hk2@HKTypeLambda(_, AppliedType(tycon2: TypeRef, _)))
        if tycon1 == tycon2 && args1.corresponds(hk2.paramRefs)((a, b) => a.hasSameKindAs(b)) =>
        val (hk2Renamed, toRenamed) = alphaRename(hk2, to.asInstanceOf[HKTypeLambda])
        assert(hk2Renamed.paramRefs == toRenamed.paramRefs)
        TECTryMatch(hk2Renamed.paramRefs.toSet, hk2Renamed.resType, target).flatMap {
          subst =>
            val substExt = subst ++ (hk2Renamed.paramRefs.toSet -- subst.keySet).map(x => x -> topOfKind(x))
            if BECSatisfied(boundsInfoOf(toRenamed), substExt) || BECSatisfied(boundsInfoOf(hk2Renamed), substExt) then
              Some(toRenamed.appliedTo(orderedSubst(toRenamed.paramRefs, substExt)))
            else
              None
        }
      case _ =>
        None

  //////////////////////////////////////////////////////////////////////

  def findOrCreateEC(t: Type)(using ctx: Context): (ECH, TypeVar) =
    val internalized = internalize(t, create = true).get
    internalized match
      case AsEC(ec) =>
        (ec, typeVarReprs(ec))
      case HKTypeLambda(params, AsAppliedEC(ec0, args)) if params.corresponds(args)((param, arg) => param.paramRef == arg) =>
        val ec = unionFind.find(ec0)
        (ec, typeVarReprs(ec))
      case _ =>
        findEquivalentMember(internalized, Nil)
          .getOrElse {
            val (newEC, _) = createEC(internalized, Nil)
            (newEC, typeVarReprs(newEC))
          }

  def internalize(t: Type, create: Boolean)(using ctx: Context): Option[Type] =
    try
      Some(doInternalize(t, Nil, create))
    catch
      case ECNotFound() => None

  def findEquivalentMember(t: Type, scope: BoundsInfo)(using Context): Option[(ECH, TypeVar)] =
    if notAppearingIn(scope.map(_._2).toSet, t) then
      val candidatesIt = allMembers.iterator
      while (candidatesIt.hasNext) do
        val candHandle = candidatesIt.next()
        val cand = storedTypes(candHandle)
        if cand.hasSameKindAs(t) && TECEquiv(cand, t) then
          val theEC = revMembers(candHandle)
          return Some((theEC, typeVarReprs(theEC)))
      None
    else None

  def doInternalize(t0: Type, scope: BoundsInfo, create: Boolean)(using ctx: Context): Type =
    def helper(t: Type, scope: BoundsInfo): Type =
      t match
        case t if t.hasSimpleKind || t.hasAnyKind =>
          findEquivalentMember(t, scope).map(_._2)
            .orElse(TECTryFindApplied(t, scope))
            .getOrElse {
              if create then createEC(t, scope)._2
              else throw ECNotFound()
            }
        // TODO: After all, could we call TECTryFindApplied for HK types as well?
        case hk: HKTypeLambda =>
          findEquivalentMember(t, scope).map(_._2)
            .getOrElse {
              if create then createEC(t, scope)._2
              else throw ECNotFound()
            }
    end helper

    val t = etaExpandIfNeeded(t0)
    t match
      // TODO: There can be TypeParamRefs from a TypeVar
      // TODO: If it comes from a typevar, couldn't we just wrap it up again in that typevar ? (may be stripped by TypeComparer...)
      case t: TypeParamRef if scope.exists(_._2 == t) => t

      case tb@TypeBounds(lo, hi) =>
        TypeBounds(doInternalize(lo, scope, create), doInternalize(hi, scope, create))

      // TODO: LazyRef ok?
      case lr: LazyRef => doInternalize(lr.ref, scope, create)

      // TODO: RecType ok?
      case rec: RecType => doInternalize(rec.parent, scope, create)

      case AppliedType(tycon, args) =>
        val argsRec = args.map(a => doInternalize(a, scope, create))
        tycon match
          case AsEC(ec) =>
            AppliedType(typeVarReprs(ec), argsRec)
          case tr: TypeRef if tr.symbol.isClass =>
            AppliedType(tr, argsRec)
          case tv: TypeVar if tv.isInstantiated =>
            doInternalize(tv.underlying.appliedTo(argsRec), scope, create)
          case _ =>
            helper(AppliedType(tycon, argsRec), scope)

      case t: AndOrType =>
        val dnfDisjs = disjunctions(t)
        val disjsRec = mutable.Set.empty[Set[Type]]
        for (disj <- dnfDisjs) {
          val conjsRec = mutable.Set.empty[Type]
          for (conj <- disj) {
            conjsRec += doInternalize(conj, scope, create)
//            conj match
//              case AppliedType(tycon: TypeRef, args) if tycon.symbol.isClass =>
//                val argsRec = args.map(a => TFindOrCreateEC(a, scope, false, create))
//                conjsRec += AppliedType(tycon, argsRec)
//              case t: TypeRef if t.symbol.isClass =>
//                conjsRec += t
//              case conj =>
//                conjsRec += TFindOrCreateEC(conj, scope, create)
          }
          disjsRec += conjsRec.toSet
        }
        // TODO: Must simplify first
        disjunctionsToType(disjsRec.toSet)

      // TODO: What if an external tyvar gets instantiated "behind our back"???
      case AsEC(ec) => typeVarReprs(ec)

      case tv: TypeVar =>
        if tv.isInstantiated then
          doInternalize(tv.underlying, scope, create)
        else
          helper(tv, scope)

      case tr: TypeRef =>
        if tr.symbol.isClass then tr
        else helper(tr, scope)

      case hk: HKTypeLambda =>
        val hkBoundsInfo = boundsInfoOf(hk)
        val hkBoundsRec = doInternalizeBounds(hkBoundsInfo, scope, create)
        hk.resType match
          // [X] =>> ec[X]
          // TODO: What about the bounds?
          // Captured by AsEC
//          case AsAppliedEC(ec, args) if args == hkBoundsInfo.map(_._2) =>
//            typeVarReprs(ec)
          // [X] =>> TyCon[X]
          case AppliedType(tycon: TypeRef, args) if args == hkBoundsInfo.map(_._2) =>
            helper(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), hk.resType), scope)
          // [X] =>> TV[X]
          case AppliedType(tycon: TypeVar, args) if args == hkBoundsInfo.map(_._2) && !tycon.isInstantiated =>
            helper(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), hk.resType), scope)
          case _ =>
            val bodyRec = doInternalize(hk.resType, scope ++ hkBoundsRec, create)
            helper(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), bodyRec), scope)
        /*
        hk.resType match
          // [X] =>> ec[X]
          case AppliedType(ECTypeVar(ec), args) if args == hkBoundsInfo.map(_._2) =>
            typeVarReprs(ec)
          // [X] =>> TyCon[X]
          case AppliedType(tycon: TypeRef, args) if args == hkBoundsInfo.map(_._2) =>
             helper(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), hk.resType), scope, create)
          case AppliedType(tycon: TypeVar, args) if args == hkBoundsInfo.map(_._2) && !tycon.isInstantiated =>
             helper(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), hk.resType), scope, create)
          case _ =>
            // TODO: What if body not of simple kind ?
            val bodyRec = TFindOrCreateEC(hk.resType, scope ++ hkBoundsRec, create)
            helper(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), bodyRec), scope, create)
        */
      case tr: TermRef =>
        // TODO: What to do with this??? should we access "underlying"???
        helper(tr, scope)

      case tr: ConstantType =>
        // TODO: What to do with this??? should we access "underlying"???
        helper(tr, scope)

      case other =>
//        println(i"TFindECOrCreate other match: EC For $other:")
//        println(s"   $other")
        val res = helper(other, scope)
//        println(i"For that type, result is: $res")
        res

  def doInternalizeBounds(hkBounds: BoundsInfo, enclosingBounds: BoundsInfo, create: Boolean)(using Context): BoundsInfo =
    val boundsTmp = enclosingBounds ++ hkBounds.map {
      case (v, tyParam, _) => (v, tyParam, TypeBounds.upper(topOfKind(tyParam)))
    }
    hkBounds.map { case (v, tyName, tb) =>
      val loRec = doInternalize(tb.lo, boundsTmp, create)
      val hiRec = doInternalize(tb.hi, boundsTmp, create)
      (v, tyName, TypeBounds(loRec, hiRec))
    }

  def createEC(t: Type, scope: BoundsInfo)(using ctx: Context): (ECH, Type) =
    val newEC = unionFind.add()
    // TODO: Do not store anything if t is a TyVar!
    val (typeToStore: Type, tyVarRepr: TypeVar, typeToReturn: Type) = {
      val x = 3
      t match
        case t if t.hasSimpleKind || t.hasAnyKind =>
          if notAppearingIn(scope.map(_._2).toSet, t) then
            val tyVarRepr = unconstrainedTypeVar(defn.AnyType)
            t match
              // TODO: Explain why
              case tv: TypeVar =>
                ext2int += tv -> tyVarRepr
                int2ext += tyVarRepr -> tv
                (NoType, tyVarRepr, tyVarRepr)
              case _ =>
                (t, tyVarRepr, tyVarRepr)
          else
            val tyVarRepr = unconstrainedTypeVar(scope.map(_._3.hi))
            // - For typeToStore, we need to create [vX <| BX] =>> T
            //   ~~> We need to substitute the typeparamref with new syntectic names
            // - For returnedType, we need to create [newEC][X]  <--- the "X" here are the X in scope, not of the HK
            (closeOver(t, scope), tyVarRepr, AppliedType(tyVarRepr, scope.map(_._2)))

        case hk: HKTypeLambda =>
          if notAppearingIn(scope.map(_._2).toSet, hk) then
            val tyVarRepr = unconstrainedTypeVar(hk)
            // TODO: Is this even correct???
            hk.resType match
              // TODO: Explain why
              case tv: TypeVar =>
                ext2int += tv -> tyVarRepr
                int2ext += tyVarRepr -> tv
                (NoType, tyVarRepr, tyVarRepr)
              // TODO: Explain why
              // TODO: Explain why
              // TODO: Explain why: we must have a 1-to-1 correspondance between [X] =>> internalTV[X] and [X] =>> extTV[X], if the args of extTV are different, we no longer have internal == external
              case AppliedType(tv: TypeVar, args) if args == hk.paramRefs =>
                ext2int += tv -> tyVarRepr
                int2ext += tyVarRepr -> tv
                (NoType, tyVarRepr, tyVarRepr)
              case resTy =>
                (hk, tyVarRepr, tyVarRepr)
          else
            // TODO: Verify this thing
            val hkBoundsInfo = boundsInfoOf(hk)
            val newHKBoundsInfo = scope ++ hkBoundsInfo
            val tyVarRepr = unconstrainedTypeVar(newHKBoundsInfo.map(_._3.hi))
            (closeOver(hk.resType, newHKBoundsInfo),
              tyVarRepr,
              closeOver(AppliedType(tyVarRepr, newHKBoundsInfo.map(_._2)), hkBoundsInfo))
    }

    // TODO: Ugly
    if typeToStore.exists then
      val storedTypeTH = TH.fromInt(thCounter)
      thCounter += 1
      members += newEC -> mutable.Set(storedTypeTH)
      revMembers += storedTypeTH -> newEC
      storedTypes += storedTypeTH -> typeToStore
      typeVarReprs += newEC -> tyVarRepr
      revTypeVarReprs += tyVarRepr -> newEC
      if isDet(typeToStore) then
        dets += newEC -> storedTypeTH
    else
      members += newEC -> mutable.Set.empty
      typeVarReprs += newEC -> tyVarRepr
      revTypeVarReprs += tyVarRepr -> newEC

    (newEC, typeToReturn)

  // TODO: Ensure of simple kind
  def TECTryFindApplied(t: Type, bounds: BoundsInfo)(using Context): Option[Type] =
    t match
      case _: (TypeVar | TypeRef) => None
      case t =>
        val candidatesIt = allMembers.iterator
        while (candidatesIt.hasNext) {
          val h = candidatesIt.next()
          storedTypes(h) match
            case hk: HKTypeLambda =>
              TECTryMatch(hk.paramRefs.toSet, hk.resType, t) match
                case Some(subst) =>
                  val substExt = subst ++ (hk.paramRefs.toSet -- subst.keySet).map(x => x -> topOfKind(x))
                  if BECSatisfied(boundsInfoOf(hk), substExt) then
                    val substImgOrdered = orderedSubst(hk.paramRefs, substExt)
                    val ecTyVar = typeVarReprs(revMembers(h))
                    val applied = AppliedType(ecTyVar, substImgOrdered)

                    if notAppearingIn(bounds.map(_._2).toSet, t) && noTypeParams(applied) then
                      TECTryFindECOfApplied(revMembers(h), substImgOrdered) match
                        case Some(ec) => return Some(typeVarReprs(ec))
                        case None => ()
                    // TODO: different from original (if !notAppearing removed)
                    return Some(applied)
                case None => ()
            case _ => ()
        }
        None

  def TECTryFindECOfApplied(tyconEC: ECH, args: List[Type])(using Context): Option[ECH] =
    val candidatesIt = allMembers.iterator
    while (candidatesIt.hasNext) {
      val h = candidatesIt.next()
      storedTypes(h) match
        case AsAppliedEC(candEC, candArgs)
          if unionFind.find(candEC) == unionFind.find(tyconEC) &&
            candArgs.corresponds(args)(TECEquiv) =>
          return Some(revMembers(h))
        case _ => ()
    }
    None


  //////////////////////////////////////////////////////////////////////////////////

  def isDet(t: Type)(using ctx: Context): Boolean =
    t match
      case t: AndOrType =>
        val disjsSet = disjunctions(t)
        if !disjsSet.forall(_.forall(isDet)) then
          return false
        val disjs = disjsSet.map(conj => conj.reduce(AndType.make(_, _)))

        val combinedConstraints = asConstraint

        def noSubDisjs = unordPairs(disjs).forall((disj1, disj2) =>
          !isSubtypeInFrozenConstraint(disj1, disj2, combinedConstraints) &&
            !isSubtypeInFrozenConstraint(disj2, disj1, combinedConstraints))

        def noSubConjs = disjsSet.forall(conj =>
          unordPairs(conj).forall((t1, t2) =>
            !isSubtypeInFrozenConstraint(t1, t2, combinedConstraints) &&
              !isSubtypeInFrozenConstraint(t2, t1, combinedConstraints)))

        noSubDisjs && noSubConjs
      case AppliedType(tycon: TypeRef, _) if tycon.symbol.isClass =>
        true
      case t: TypeRef if t.symbol.isClass =>
        true
      case hk: HKTypeLambda =>
        isDet(hk.resType)
      case AsEC(ec) =>
        dets.get(ec).isDefined
      case t =>
        isDetSingleHead(t)

  def isDetSingleHead(t: Type)(using Context): Boolean =
    assert(!t.isInstanceOf[AndOrType])
    assert(!t.isInstanceOf[HKTypeLambda])
    t match
      case AppliedType(tycon: TypeRef, _) if tycon.symbol.isClass =>
        true
      case t: TypeRef if t.symbol.isClass =>
        true
      case AsEC(ec) =>
        dets.get(ec).isDefined
      case _: ConstantType => true
      case _ =>
        t.isAny || t.isAnyRef || t.isNothingType

  def isWeaklyDet(t: Type)(using Context): Boolean =
    t match
      case t: AndOrType =>
        disjunctions(t).forall(_.forall(isDetSingleHead))
      case hk: HKTypeLambda =>
        isWeaklyDet(hk.resType)
      case t =>
        isDetSingleHead(t)

  //////////////////////////////////////////////////////////////////////////////////

//  def TECEquiv(t: Type, s: Type)(using ctx: Context): Boolean =
//    val combinedConstraints = asConstraint
//    isSameInFrozenConstraint(t, s, combinedConstraints)

  // TODO: Assumes dealias and all these things are already taken care of (applies to HK Bounds as well)
  def TECEquiv(s: Type, t: Type)(using ctx: Context): Boolean =
    def helper(ecA: ECH, other: Type): Boolean =
      members(unionFind.find(ecA)).exists(candTH => TECEquiv(storedTypes(candTH), other))

    if !s.hasSameKindAs(t) then
      return false

    (s, t) match
      case (AsEC(ecS), AsEC(ecT)) =>
        ecS == ecT

      case (AsAppliedEC(ecS, argsS), AsAppliedEC(ecT, argsT)) =>
        ecS == ecT && argsS.corresponds(argsT)(TECEquiv(_, _))

      case (AsEC(ecS), t) =>
        helper(ecS, t)

      case (s, AsEC(ecT)) =>
        helper(ecT, s)

      case (AppliedType(tyconS, argsS), AppliedType(tyconT, argsT)) =>
        tyconS == tyconT && argsS.corresponds(argsT)(TECEquiv(_, _))

      case (hkS: HKTypeLambda, hkT: HKTypeLambda) =>
        Variances.variancesConform(hkS.typeParams, hkT.typeParams)
          && hkS.typeParams.corresponds(hkT.typeParams) { (tparamS, tparamT) =>
            val TypeBounds(hkSLo, hkSHi) = tparamS.paramInfo.bounds
            val TypeBounds(hkTLo, hkTHi) = tparamT.paramInfo.subst(hkT, hkS).bounds
            TECEquiv(hkSLo, hkTLo) && TECEquiv(hkSHi, hkTHi)
          } && TECEquiv(hkS.resType, hkT.resType.subst(hkT, hkS))

      case (s: AndOrType, t: AndOrType) =>
        // TODO: Don't be lazy and do this properly!!!!!!
        // TODO: Don't be lazy and do this properly!!!!!!
        // TODO: Don't be lazy and do this properly!!!!!!
        TECIsSubtype(s, t) && TECIsSubtype(t, s)

      case _ => s == t

  def TECIsSubtype(s: Type, t: Type)(using ctx: Context): Boolean =
    def isSubArgs(variances: List[Variance], argsA: List[Type], argsB: List[Type]): Boolean =
      assert(variances.hasSameLengthAs(argsA))
      assert(argsA.hasSameLengthAs(argsB))
      variances.zip(argsA).corresponds(argsB) {
        case ((v, argA), argB) if varianceToInt(v) > 0 =>
          TECIsSubtype(argA, argB)
        case ((v, argA), argB) if varianceToInt(v) < 0 =>
          TECIsSubtype(argB, argA)
        case ((_, argA), argB) =>
          TECEquiv(argA, argB)
      }

    // TODO: Verify if this is correct
    def varianceOfEC(ec: ECH): List[Variance] =
      typeVarReprs(ec).typeParams.map(_.paramVariance)

    ///////////////////////////////////////////////////

    if !s.hasSameKindAs(t) then
      return false

    if s.isNothingType || t.isAny then
      return true

    (s, t) match
      case (s, t: AndType) =>
        TECIsSubtype(s, t.tp1) && TECIsSubtype(s, t.tp2)

      case (s: OrType, t) =>
        TECIsSubtype(s.tp1, t) && TECIsSubtype(s.tp2, t)

      case (s, t: OrType) =>
        TECIsSubtype(s, t.tp1) || TECIsSubtype(s, t.tp2)

      case (s: AndType, t) =>
        TECIsSubtype(s.tp1, t) || TECIsSubtype(s.tp2, t)

      case (AsClassOrTrait(clsS, argsS), AsClassOrTrait(clsT, argsT)) =>
        val variances = clsS.typeParams.map(_.paramVariance)
        if clsS == clsT then
          isSubArgs(variances, argsS, argsT)
        else if clsS.derivesFrom(clsT) then
          val (upcastedS, _) = upcastTo(clsS, argsS, clsT)
          upcastedS.exists(TECIsSubtype(_, t))
        else
          // TODO: This false denotes "subtyping impossibilty", which is stronger than uncertainty (that is denoted by false as well...)
          false

      case (AsEC(ecS), AsEC(ecT)) =>
//        def byDet =
//          dets.get(ecS).zip(dets.get(ecT))
//            .map((detS, detT) => TECIsSubtype(storedTypes(detS), storedTypes(detT)))
//            .getOrElse(false)
        def byWeaklyDets =
          cartesian(weaklyDetsOf(ecS), weaklyDetsOf(ecT))
            .exists(TECIsSubtype(_, _))

        ecS == ecT || gSub.chain(ecS, ecT).isEmpty || byWeaklyDets

      case (AsAppliedEC(ecS, argsS), AsAppliedEC(ecT, argsT)) =>
        if !Variances.variancesConform(typeVarReprs(ecS).typeParams, typeVarReprs(ecT).typeParams) then
          return false
        if ecS == ecT || gSub.chain(ecS, ecT).isDefined then
          // Note: for the case where ecS != ecT but ecS <: ecT, we know that ecS and ecT have the same kind
          // (otherwise, we would have returned earlier), so argsS and argsT have the same length.
          isSubArgs(varianceOfEC(ecS), argsS, argsT)
        else
          // TODO: explain why bounds are tested all over again
          cartesian(weaklyDetsOf(ecS), weaklyDetsOf(ecT)).exists {
            case (membS: HKTypeLambda, membT: HKTypeLambda) =>
              val boundsOK = membS.typeParams.corresponds(membT.typeParams) { (tparamS, tparamT) =>
                val TypeBounds(membSLo, membSHi) = tparamS.paramInfo.bounds
                val TypeBounds(membTLo, membTHi) = tparamT.paramInfo.subst(membT, membS).bounds
                TECIsSubtype(membSLo, membTLo) && TECIsSubtype(membTHi, membSHi)
              }
              boundsOK && TECIsSubtype(membS.appliedTo(argsS), membT.appliedTo(argsT))
            case _ => false // should be unreachable because ecS and ecT must be higher-kinded in order to be applied
          }

      case (s: HKTypeLambda, t: HKTypeLambda) =>
        if !Variances.variancesConform(s.typeParams, t.typeParams) then
          return false
        val boundsOK = s.typeParams.corresponds(t.typeParams) { (tparamS, tparamT) =>
          val TypeBounds(sLo, sHi) = tparamS.paramInfo.bounds
          val TypeBounds(tLo, tHi) = tparamT.paramInfo.subst(t, s).bounds
          TECIsSubtype(sLo, tLo) && TECIsSubtype(tHi, sHi)
        }
        boundsOK && TECIsSubtype(s.resType, t.resType.subst(t, s))

      case (AppliedType(tyconS, argsS), AppliedType(tyconT, argsT)) =>
        tyconS == tyconT && isSubArgs(tyconS.typeParams.map(_.paramVariance), argsS, argsT)

      case (AsEC(ecS), t) =>
        weaklyDetsOf(ecS).exists(TECIsSubtype(_, t))

      case (s, AsEC(ecT)) =>
        weaklyDetsOf(ecT).exists(TECIsSubtype(s, _))

      case (AsAppliedEC(ecS, argsS), t) =>
        weaklyDetsOf(ecS).exists(membS => TECIsSubtype(membS.appliedTo(argsS), t))

      case (s, AsAppliedEC(ecT, argsT)) =>
        weaklyDetsOf(ecT).exists(membT => TECIsSubtype(s, membT.appliedTo(argsT)))

      case _ => s == t

  // TODO: Marche assui avec refn on dirait ?
  def BSubsumes(l: BoundsInfo, r: BoundsInfo)(using ctx: Context): Boolean =
    assert(l.corresponds(r) { case ((vl, tl, _), (vr, tr, _)) => vl == vr && tl.hasSameKindAs(tr) })

    // TODO: Nein!!!
    // TODO: Nein!!!
    // TODO: Nein!!!
    // TODO: Nein!!!
    val newParams: List[TypeVar] = l.map((_, ty, _) => unconstrainedTypeVar(ty))
    val map = l.map(_._2).zip(newParams).toMap ++ r.map(_._2).zip(newParams).toMap
    val typeMap = new TypeMap {
      override def apply(tp: Type): Type = tp match
        case tp: TypeParamRef =>
          map.getOrElse(tp, mapOver(tp))
        case t => mapOver(t)
    }
    val combinedConstraints = asConstraint
    l.map(_._3).zip(r.map(_._3)).forall {
      case (TypeBounds(lo1, hi1), TypeBounds(lo2, hi2)) =>
        isSubtypeInFrozenConstraint(typeMap(lo2), typeMap(lo1), combinedConstraints) &&
          isSubtypeInFrozenConstraint(typeMap(hi2), typeMap(hi1), combinedConstraints)
    }

  // TODO: Marche aussi avec refn on dirait ?
  def BEntailed(bnds: BoundsInfo)(using Context): Boolean =
    val combinedConstraints = asConstraint
    bnds.forall {
      case (_, _, TypeBounds(lo, hi)) =>
        isSubtypeInFrozenConstraint(lo, hi, combinedConstraints)
    }

  def BECEquiv(l: BoundsInfo, r: BoundsInfo)(using Context): Boolean =
    assert(l.corresponds(r) { case ((_, tl, _), (_, tr, _)) => tl.hasSameKindAs(tr) })

    def isEquiv =
      // TODO: Nein!!!
      // TODO: Nein!!!
      // TODO: Nein!!!
      // TODO: Nein!!!
      val newParams: List[TypeVar] = l.map((_, ty, _) => unconstrainedTypeVar(ty))
      val map = l.map(_._2).zip(newParams).toMap ++ r.map(_._2).zip(newParams).toMap
      val typeMap = new TypeMap {
        override def apply(tp: Type): Type = tp match
          case tp: TypeParamRef =>
            map.getOrElse(tp, mapOver(tp))
          case t => mapOver(t)
      }
      l.map(_._3).zip(r.map(_._3)).forall {
        case (TypeBounds(lo1, hi1), TypeBounds(lo2, hi2)) =>
          TECEquiv(typeMap(lo1), typeMap(lo2)) &&
            TECEquiv(typeMap(hi1), typeMap(hi2))
      }

    l.map(_._1) == r.map(_._1) && isEquiv

  def BECSatisfied(bounds: BoundsInfo, subst: Map[TypeParamRef, Type])(using ctx: Context): Boolean =
    assert(bounds.map(_._2).toSet == subst.keySet)
    val typeMap = new TypeMap {
      override def apply(tp: Type): Type =
        tp match
          case tp: TypeParamRef =>
            subst.get(tp) match
              case Some(t) => t
              case None => mapOver(tp)
          case tp => mapOver(tp)
    }
    val combinedConstraints = asConstraint
    bounds.forall { case (_, tyParamRef, TypeBounds(lo, hi)) =>
      isSubtypeInFrozenConstraint(typeMap(lo), subst(tyParamRef), combinedConstraints) &&
        isSubtypeInFrozenConstraint(subst(tyParamRef), typeMap(hi), combinedConstraints)
    }

  //////////////////////////////////////////////////////////////////////

  def TECTryMatch(xs: Set[TypeParamRef], t: Type, s: Type)(using Context): Option[Map[TypeParamRef, Type]] =
    // assert(ftv(s).intersect(xs).isEmpty)
    // TODO: do we need this as a requirement? It seems too depending, for instance, we couldn't even match a body of an HK abstraction with itself
//    assert(notAppearingIn(xs, s))
    // if ftv(t).intersect(xs).isEmpty then
    if notAppearingIn(xs, t) then
      if TECEquiv(t, s) then
        Some(Map.empty)
      else
        None
    try
      val res = TECTryMatchImpl(xs, t, s)
      Some(res)
    catch
      case TryMatchFail() => None

  def TECTryMatchImpl(xs: Set[TypeParamRef], t: Type, s: Type)(using Context): Map[TypeParamRef, Type] =
    if notAppearingIn(xs, t) then
      if TECEquiv(t, s) then
        Map.empty
      else
        throw TryMatchFail()

    (t, s) match
      //      case (t: AndOrType, s) =>
      //        TECTryMatchImpl(xs, toDNF(t), s)
      //      case (t, s: AndOrType) =>
      //        TECTryMatchImpl(xs, t, toDNF(s))
      case (t: TypeParamRef, s) if xs.contains(t) => Map(t -> s)

      case (AsAppliedEC(ec1, args1), AsAppliedEC(ec2, args2)) if ec1 == ec2 =>
        TECTryMatchVec(xs, args1, args2)

      // TODO: tycon comp. a bit too restrictive ?
      case (AppliedType(tycon1, args1), AppliedType(tycon2, args2)) if tycon1 == tycon2 =>
        TECTryMatchVec(xs, args1, args2)

      case (hk1: HKTypeLambda, hk2: HKTypeLambda) =>
        assert(hk1.paramNames.size == hk2.paramNames.size)
        // TODO: Ok w.r.t. tyvar that are not "fresh" and that hk1 and hk2 var are not the same ?
        val hk1Vars = hk1.paramRefs.toSet
        val hk2Vars = hk2.paramRefs.toSet
        // TODO: No, must substitute one of the hk body with one of the other binder (see isSubtype)
        val substBody = TECTryMatchImpl(xs ++ hk1Vars, hk1.resType, hk2.resType)
        val subst = (0 until hk1.paramNames.size)
          .map(i => (hk1.paramInfos(i), hk2.paramInfos(i)))
          .foldLeft(substBody) {
            case (substAcc, (TypeBounds(lo1, hi1), TypeBounds(lo2, hi2))) =>
              val substLo = TECTryMatchImpl(xs ++ hk1Vars, lo1, lo2)
              val substHi = TECTryMatchImpl(xs ++ hk1Vars, hi1, hi2)
              TECTryCombineSubstMatch(substAcc, TECTryCombineSubstMatch(substLo, substHi))
          }
        val (substHKParams, substXs) = subst.partition((tyParam, _) => hk1Vars.contains(tyParam))
        //        val substXsFtv = substXs.values.flatMap(ftv).toSet
        //        if substHKParams.values.toSet == hk2Vars && substXsFtv.intersect(hk1Vars ++ hk2Vars).isEmpty then
        if substHKParams.values.toSet == hk2Vars
          && substXs.values.forall(t => notAppearingIn(hk1Vars ++ hk2Vars, t)) then
          substXs
        else
          throw TryMatchFail()

      case (t: AndOrType, s: AndOrType) =>
        val tDisjsSorted: Vector[Set[Type]] = disjunctions(t).toVector.sortBy(_.size)
        val sDisjsSorted: Vector[Set[Type]] = disjunctions(s).toVector.sortBy(_.size)
        if tDisjsSorted.map(_.size) != sDisjsSorted.map(_.size) then
          throw TryMatchFail()
        val disjsSameSize = tDisjsSorted.indices.groupBy(tDisjsSorted(_).size)
        disjsSameSize.foldLeft(Option.empty[Map[TypeParamRef, Type]]) {
          case (substAcc, (_, disjsIndices)) =>
            disjsIndices.flatMap(i1 => disjsIndices.map(i2 => (i1, i2)))
              .foldLeft(substAcc) { case (substConjAcc, (i1, i2)) =>
                try
                  val substConj = TECTryMatchConjunct(xs, tDisjsSorted(i1), sDisjsSorted(i2))
                  substConjAcc match
                    case Some(substConjAcc) =>
                      if !TECEquivSubstMatch(substConjAcc, substConj) then
                        None
                      else Some(substConjAcc)
                    case None => Some(substConj)
                catch
                  case TryMatchFail() => substConjAcc
              }
        }.getOrElse(throw TryMatchFail())

      case _ =>
        throw TryMatchFail()

  def TECEquivSubstMatch(l: Map[TypeParamRef, Type], r: Map[TypeParamRef, Type])(using Context): Boolean =
    l.keySet == r.keySet && l.keySet.forall(tyParam => TECEquiv(l(tyParam), r(tyParam)))

  def TECTryMatchConjunct(xs: Set[TypeParamRef], t: Set[Type], s: Set[Type])(using Context): Map[TypeParamRef, Type] =
    t.flatMap(t => s.map(s => (t, s)))
      .foldLeft(Option.empty[Map[TypeParamRef, Type]]) { case (substConjAcc, (t, s)) =>
        try
          val substConj = TECTryMatchImpl(xs, t, s)
          substConjAcc match
            case Some(substConjAcc) =>
              if !TECEquivSubstMatch(substConjAcc, substConj) then
                None
              else Some(substConjAcc)
            case None => Some(substConj)
        catch
          case TryMatchFail() => substConjAcc
      }.getOrElse(throw TryMatchFail())

  def TECTryCombineSubstMatch(l: Map[TypeParamRef, Type], r: Map[TypeParamRef, Type])(using Context): Map[TypeParamRef, Type] =
    val inCommon = l.keySet.intersect(r.keySet)
    val disjoint = (l.keySet ++ r.keySet) -- inCommon
    if !inCommon.forall(tyParam => TECEquiv(l(tyParam), r(tyParam))) then
      throw TryMatchFail()
    l ++ r

  def TECTryMatchVec(xs: Set[TypeParamRef], t: Seq[Type], s: Seq[Type])(using Context): Map[TypeParamRef, Type] =
    assert(t.size == s.size)
    t.zip(s).foldLeft(Map.empty) {
      case (acc, (t, s)) => TECTryCombineSubstMatch(acc, TECTryMatchImpl(xs, t, s))
    }

  //////////////////////////////////////////////////////////////////////

  def allInternalTyVarsOf(ec: ECH): Set[TypeVar] =
    revTypeVarReprs.filter((_, cand) => cand == ec).map(_._1).toSet


  class ECPrinter(ctx: Context) extends RefinedPrinter(ctx):
    override def toText(t: Type): Text =
      t match
        // TODO: May need to to someting similar for applied ec?
        case AsEC(ec) =>
          Str(s"[$ec]")
        case tv: TypeVar => Str(tv.toString)
        case _ => super.toText(t)

  def debugString(using ctx: Context): String =
    if members.isEmpty then
      return "(empty K)"

    val printer = new ECPrinter(ctx)

    val ecsContent =
      members.foldLeft(Seq.empty[String]) {
        case (acc, (ec, membs)) =>
          val membsSorted = membs.toSeq.sortBy(_.toInt)
          val tys = membsSorted.map(th => storedTypes(th).toText(printer).show).mkString(", ")
          val tyVars = allInternalTyVarsOf(ec)
          val extTyVars = tyVars.flatMap(int2ext.get).map(_.toString).mkString(", ")
          val symbols = symsEC.filter((_, candEC) => candEC == ec).map(_._1.toText(printer).show).mkString(", ")

          acc :+
            s"""$ec: {$tys} (THs: {${membsSorted.mkString(",")}}, """ ++
            s"""internal tvs: {${tyVars.map(_.toString).mkString(", ")}}, """ ++
            s"""ext tvs: {$extTyVars}, symbols: {$symbols})"""
      }.mkString("\n")

    val detsContent =
      if dets.nonEmpty then "Dets: " ++ dets.map((ec, detTH) => s"[$ec] -> " ++ storedTypes(detTH).toText(printer).show).mkString(", ")
      else "(no dets)"

    val cst = asConstraint
    ecsContent ++ "\n" ++ detsContent ++ "\n" ++ gSub.debugString ++ "\n" ++ cst.show


case class TryMatchFail() extends Exception

case class ECNotFound() extends Exception
