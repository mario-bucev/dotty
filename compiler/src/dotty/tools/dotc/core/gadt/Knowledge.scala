package dotty.tools
package dotc
package core
package gadt

import ExtraTypes._
import Variances._
import UnionFind._
import Types._
import Names._
import Decorators._
import Contexts._
import Symbols._
import typer.ProtoTypes.newTypeVar
import Utils._
import scala.collection.mutable

opaque type TH = Int

object TH:
  def fromInt(v: Int): TH = v


class Knowledge:
  val unionFind = new UnionFind
  val gSub = new GSub
  val members: mutable.Map[ECH, mutable.Set[TH]] = mutable.Map.empty
  val storedTypes: mutable.Map[TH, Type] = mutable.Map.empty
  val ecOf: mutable.Map[TH, ECH] = mutable.Map.empty
  val dets: mutable.Map[ECH, TH] = mutable.Map.empty
  val typeVarRepr: mutable.Map[ECH, TypeRef] = mutable.Map.empty


  def allMembers: Set[TH] =
    members.values.flatMap(_.toSet).toSet

  // TODO
  def compact(s: Type, t: Type) = ???

  // TODO
  def deduce(s: Type, t: Type): Set[(Type, Type)] = ???

  def TFindOrCreateEC(t: Type,
    bounds: BoundsInfo,
    inHead: Boolean,
    create: Boolean)(using Context): Type =
    println(s"TFindOrCreateEC: $t")
    t match
      case t: TypeParamRef =>
        // TODO: Même si higher-kinded ? ~> il semblerait que oui
        t

      case AppliedType(tycon, args) =>
        val argsRec = args.map(a => TFindOrCreateEC(a, bounds, false, create))
        tycon match
          case _: TypeParamRef =>
            // HK type bounded in an enclosing HK
            AppliedType(tycon, argsRec)
          case tycon: TypeRef =>
            if tycon.symbol.isClass then AppliedType(tycon, argsRec)
            else TECFindOrCreateEC(AppliedType(tycon, argsRec), bounds, create)
          case _ =>
            ???

      case t: AndOrType =>
        val dnf = toDNF(t)
        val disjsRec = mutable.Set.empty[Set[Type]]
        for (disjs <- dnf.disjunctions) {
          val conjsRec = mutable.Set.empty[Type]
          for (conj <- disjs) {
            conj match
              case AppliedType(tycon: TypeRef, args) if tycon.symbol.isClass =>
                val argsRec = args.map(a => TFindOrCreateEC(a, bounds, false, create))
                conjsRec += AppliedType(tycon, argsRec)
              case conj =>
                conjsRec += TECFindOrCreateEC(conj, bounds, create)
          }
          disjsRec += conjsRec.toSet
        }
        // TODO: Must simplify first
        val isDNF = !(disjsRec.size == 1 && disjsRec.head.size == 1)
        if isDNF && inHead && !bounds.isEmpty then
          dnf
        else
          TECFindOrCreateEC(dnf, bounds, create)

      case t: TypeRef if t.hasSimpleKind =>
        // TODO: Qu'est-ce qu'un TypeRef vraiment?
        TECFindOrCreateEC(t, bounds, create)

      case t: TypeRef =>
        TFindOrCreateEC(t.EtaExpand(t.typeParams), bounds, inHead, create)

      case hk: HKTypeLambda =>
        val hkBoundsInfo = boundsInfoOf(hk)
        val hkBoundsRec = BFindOrCreateEC(hkBoundsInfo, bounds, inHead, create)

        hk.resType match
          // TODO: Note: match aussi class/trait
          // [X] =>> TyCon[X]
          case AppliedType(tycon: TypeRef, args) if args == hkBoundsInfo.map(_._2) =>
            TECFindOrCreateEC(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), hk.resType), bounds, create)
          case _ =>
            // TODO: What if not of simple kind ?
            val bodyRec = TFindOrCreateEC(hk.resType, bounds ++ hkBoundsRec, inHead, create)
            TECFindOrCreateEC(hk.newLikeThis(hk.paramNames, hkBoundsRec.map(_._3), bodyRec), bounds, create)


  // TODO: Yikes, difficult to differentiate
  def BFindOrCreateEC(
    hkBounds: BoundsInfo,
    enclosingBounds: BoundsInfo,
    inHead: Boolean,
    create: Boolean)(using Context): BoundsInfo =
    // TODO: Bounds for higher-kinded arguments ???
    val boundsTmp = enclosingBounds ++ hkBounds.map { case (v, tyName, _) => (v, tyName, TypeBounds.empty)}
    hkBounds.map { case (v, tyName, tb) =>
      val loRec = TFindOrCreateEC(tb.lo, boundsTmp, true, create)
      val hiRec = TFindOrCreateEC(tb.hi, boundsTmp, true, create)
      (v, tyName, TypeBounds(loRec, hiRec))
    }


  def TECTryMatch(xs: Set[TypeParamRef], t: Type, s: Type)(using Context): Option[Map[TypeParamRef, Type]] =
    assert(ftv(s).intersect(xs).isEmpty)
    if ftv(t).intersect(xs).isEmpty then
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
    if ftv(t).intersect(xs).isEmpty then
      if TECEquiv(t, s) then
        Map.empty
      else
        throw TryMatchFail()

    (t, s) match
      case (t: AndOrType, s) =>
        TECTryMatchImpl(xs, toDNF(t), s)
      case (t, s: AndOrType) =>
        TECTryMatchImpl(xs, t, toDNF(s))
      case (t: TypeParamRef, s) if xs.contains(t) => Map(t -> s)
      case (t: AppliedECType, s: AppliedECType) if unionFind.find(t.ec) == unionFind.find(s.ec) =>
        TECTryMatchVec(xs, t.args, s.args)
      // TODO: tycon comp. a bit too restrictive ?
      case (AppliedType(tycon1, args1), AppliedType(tycon2, args2)) if tycon1 == tycon2 =>
        TECTryMatchVec(xs, args1, args2)
      case (hk1: HKTypeLambda, hk2: HKTypeLambda) =>
        assert(hk1.paramNames.size == hk2.paramNames.size)
        // TODO: Ok w.r.t. tyvar that are not "fresh" and that hk1 and hk2 var are not the same ?
        val hk1Vars = (0 until hk1.paramNames.size).map(hk1.paramRefs)
        val hk2Vars = (0 until hk2.paramNames.size).map(hk2.paramRefs)
        val substBody = TECTryMatchImpl(xs ++ hk1Vars.toSet, hk1.resType, hk2.resType)
        val subst = (0 until hk1.paramNames.size)
          .map(i => (hk1.paramInfos(i), hk2.paramInfos(i)))
          .foldLeft(substBody) {
            case (substAcc, (TypeBounds(lo1, hi1), TypeBounds(lo2, hi2))) =>
              val substLo = TECTryMatchImpl(xs ++ hk1Vars.toSet, lo1, lo2)
              val substHi = TECTryMatchImpl(xs ++ hk1Vars.toSet, hi1, hi2)
              TECTryCombineSubstMatch(substAcc, TECTryCombineSubstMatch(substLo, substHi))
          }
        val (substHKParams, substXs) = subst.partition((tyParam, _) => hk1Vars.contains(tyParam))
        val substXsFtv = substXs.values.flatMap(ftv).toSet
        if substHKParams.values == hk2Vars && substXsFtv.intersect(hk1Vars.toSet ++ hk2Vars.toSet).isEmpty then
          substXs
        else
          throw TryMatchFail()
      case (t: DNF, s: DNF) =>
        val tDisjsSorted: Vector[Set[Type]] = t.disjunctions.toVector.sortBy(_.size)
        val sDisjsSorted: Vector[Set[Type]] = s.disjunctions.toVector.sortBy(_.size)
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

  def TECFindOrCreateEC(
    t: Type,
    bounds: BoundsInfo,
    create: Boolean)(using Context): Type =
    t match
      case t if t.hasSimpleKind =>
        if ftv(t).intersect(bounds.map(_._2).toSet).isEmpty then
          val candidatesIt = allMembers.iterator
          while (candidatesIt.hasNext) {
            val h = candidatesIt.next()
            storedTypes.get(h) match
              case Some(s) if s.hasSimpleKind && TECEquiv(t, s) =>
                return new ECType(ecOf.get(h).get)
              case _ => ()
          }

        TECTryFindApplied(t, bounds) match
          case Some(res) => res
          case None =>
            if create then
              TECCreate(t, bounds)
            else
              throw ECNotFound()

      case hk: HKTypeLambda =>
        if ftv(t).intersect(bounds.map(_._2).toSet).isEmpty then
          val candidatesIt = allMembers.iterator
          while (candidatesIt.hasNext) {
            val h = candidatesIt.next()
            storedTypes.get(h) match
              case Some(hkCand: HKTypeLambda) if hk.hasSameKindAs(hkCand)
                && TECEquiv(hk.resType, hkCand.resType)
                && BECEquiv(boundsInfoOf(hk), boundsInfoOf(hkCand)) =>
                return new ECType(ecOf.get(h).get)
              case _ => ()
          }
        if create then
          TECCreate(t, bounds)
        else
          throw ECNotFound()

      case _ =>
        ???

  // TODO: Good enough ?
  def TECEquiv(t: Type, s: Type)(using Context): Boolean = TypeComparer.isSameTypeWhenFrozen(t, s)

  def BECEquiv(l: BoundsInfo, r: BoundsInfo)(using Context): Boolean =
    assert(l.size == r.size)
    def isEquiv =
      // TODO: gen fresh names ???
      val newParams: List[TypeRef] = ??? // List.fill(l.size)(TypeRef.apply(NoPrefix, DepParamName.fresh().toTypeName))  // HKTypeLambda.syntheticParamNames(bounds.length)
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

  def TECCreate(t: Type,
    bounds: BoundsInfo)(using Context): Type =

    val newEC = unionFind.add()
    val (typeToStore, typeVarRepr, typeToReturn) = {
      t match
        case t if t.hasSimpleKind =>
          if ftv(t).intersect(bounds.map(_._2).toSet).isEmpty then
            (t, newTypeVar(TypeBounds.empty), new ECType(newEC))
          else
            val freshHKTvar = newHKTypeVarWithBounds(bounds)
            // - For typeToStore, we need to create [vX <| BX] =>> T
            //   ~~> We need to substitute the typeparamref with new syntectic names
            // - For returnedType, we need to create [newEC][X]  <--- the "X" here are the X in bounds, not of the HK
            (closeOver(t, bounds), freshHKTvar, new AppliedECType(newEC, bounds.map(_._2)))

        case hk: HKTypeLambda =>
          val hkBoundsInfo = boundsInfoOf(hk)
          if ftv(hk).intersect(bounds.map(_._2).toSet).isEmpty then
            val freshHKTvar = newHKTypeVarWithBounds(hkBoundsInfo)
            (hk, freshHKTvar, new ECType(newEC))
          else
            val newHKBoundsInfo = bounds ++ hkBoundsInfo
            val freshHKTvar = newHKTypeVarWithBounds(newHKBoundsInfo)
            (closeOver(hk.resType, newHKBoundsInfo),
              freshHKTvar,
              closeOver(new AppliedECType(newEC, newHKBoundsInfo.map(_._2)), hkBoundsInfo))

        case _ => ???
    }

    val storedTypeTH = TH.fromInt(storedTypes.size)
    members += newEC -> mutable.Set(storedTypeTH)
    ecOf += storedTypeTH -> newEC
    storedTypes += storedTypeTH -> typeToStore
    if isDet(typeToStore) then
      dets += newEC -> storedTypeTH
    typeToReturn

  def TECTryFindApplied(t: Type,
    bounds: BoundsInfo)(using Context): Option[Type] =
    t match
      case _: (ECType | TypeRef) => None
      case t =>
        val candidatesIt = allMembers.iterator
        while (candidatesIt.hasNext) {
          val h = candidatesIt.next()
          storedTypes(h) match
            case hk: HKTypeLambda =>
              val hkParams = (0 until hk.paramNames.size).map(hk.paramRefs)
              TECTryMatch(hkParams.toSet, hk.resType, t) match
                case Some(subst) =>
                  // TODO: Top type of appr. kind
                  val substExt: Map[TypeParamRef, Type] = subst ++ (hkParams.toSet -- subst.keySet).map(x => x -> defn.AnyType)
                  if BECSatisfied(boundsInfoOf(hk), substExt) then
                    val substImgOrdered = substExt.toList.sortBy((tyParam, _) => hkParams.indexOf(tyParam)).map(_._2)
                    val applied = new AppliedECType(ecOf(h), substImgOrdered)
                    if ftv(t).intersect(bounds.map(_._2).toSet).isEmpty && ftv(applied).isEmpty then
                      TECTryFindECOfApplied(applied) match
                        case Some(ec) => return Some(new ECType(ec))
                        case None => ()
                    if ftv(t).intersect(bounds.map(_._2).toSet).nonEmpty then
                      return Some(applied)
                case None => ()
            case _ => ()
        }
        None

  def TECTryFindECOfApplied(t: AppliedECType)(using Context): Option[ECH] =
    val candidatesIt = allMembers.iterator
    while (candidatesIt.hasNext) {
      val h = candidatesIt.next()
      storedTypes(h) match
        case cand: AppliedECType if unionFind.find(t.ec) == unionFind.find(cand.ec) =>
          return Some(ecOf(h))
        case _ => ()
    }
    None

  def BECSatisfied(bounds: BoundsInfo, subst: Map[TypeParamRef, Type])(using Context): Boolean =
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
    bounds.forall { case (_, tyParamRef, TypeBounds(lo, hi)) =>
      TypeComparer.isSubTypeWhenFrozen(typeMap(lo), subst(tyParamRef)) &&
      TypeComparer.isSubTypeWhenFrozen(subst(tyParamRef), typeMap(hi))
    }


  //////////////////////////////////////////////////////////////////////////////////

  // TODO
  def typeReprOf(ec: ECH): Type = ???

  def isDet(t: Type)(using Context): Boolean =
    t match
      case dnf: DNF if dnf.disjunctions.forall(_.forall(isDet)) =>
        val disjs = dnf.disjunctions.map(conj => conj.reduce(AndType.make(_, _)))
        def noSubDisjs = unordPairs(disjs).forall((disj1, disj2) =>
          TypeComparer.isSubTypeWhenFrozen(disj1, disj2) &&
          TypeComparer.isSubTypeWhenFrozen(disj2, disj1))
        def noSubConjs = dnf.disjunctions.forall(conj =>
          unordPairs(conj).forall((t1, t2) =>
            TypeComparer.isSubTypeWhenFrozen(t1, t2) &&
            TypeComparer.isSubTypeWhenFrozen(t2, t1)))
        noSubDisjs && noSubConjs
      // TODO: Et les gnd types ???
      case AppliedType(tycon: TypeRef, _) if tycon.symbol.isClass =>
        true
      case t: TypeRef if t.symbol.isClass =>
        true
      case hk: HKTypeLambda =>
        isDet(hk.resType)
      case _ =>
        false


case class TryMatchFail() extends Exception

case class ECNotFound() extends Exception
