package dotty.tools
package dotc
package core
package gadt

import Variances._
import UnionFind._
import Types._
import Names._
import Decorators._
import Contexts._
import Symbols._
import Flags._
import typer.ProtoTypes.newTypeVar
import Utils._
import scala.collection.mutable

opaque type TH = Int

object TH:
  def fromInt(v: Int): TH = v

extension (th: TH)
  def toInt: Int = th

class Knowledge:
  val unionFind = new UnionFind
  val gSub = new GSub
  val members: mutable.Map[ECH, mutable.Set[TH]] = mutable.Map.empty

  // TODO: If adding fields, remember to updade merge if needed
  val storedTypes: mutable.Map[TH, Type] = mutable.Map.empty
  var thCounter: Int = 0
  val ecOf: mutable.Map[TH, ECH] = mutable.Map.empty
  val dets: mutable.Map[ECH, TH] = mutable.Map.empty

  val typeVarReprs: mutable.Map[ECH, TypeVar] = mutable.Map.empty
  val typeVarEC: mutable.Map[TypeVar, ECH] = mutable.Map.empty

  //////////////////////////////////////////////////////////////////////

  // TODO: Is this even idiomatic ???
  object ECTypeVar:
    def unapply(tv: TypeVar): Option[ECH] =
      // TODO: Pas de qfind fait !! A faire manuellement
      // TODO: ~> en fait pas besoin, merge s'en occupe
      typeVarEC.get(tv)

  object AppliedECTypeVar:
    def unapply(app: AppliedType): Option[(ECH, List[Type])] =
      app match
        case AppliedType(ECTypeVar(ec), args) => Some((ec, args))
        case _ => None

  //////////////////////////////////////////////////////////////////////

  def allMembers: Set[TH] =
    members.values.flatMap(_.toSet).toSet

  def weaklyDetsOf(a: ECH)(using Context): Set[Type] =
    members(a).toSet.map(storedTypes).filter(isWeaklyDet)

  def removeMember(th: TH): Unit =
    val ec = ecOf(th)
    ecOf -= th
    members(ec) -= th
    if dets.get(ec).exists(_ == th) then
      dets -= ec

  // TODO: to enhance
  def updateMemberDet(th: TH, ty: Type)(using ctx: Context): (Set[(Type, Type)], Set[(ECH, ECH)], Set[ECH]) =
    val ecOfTh = ecOf(th)
    dets.get(ecOfTh) match
      case Some(detTh) if detTh != th =>
        val detTy = storedTypes(detTh)
        val cstrts = Set((detTy, ty), (ty, detTy))
        removeMember(th)
        (cstrts, Set.empty, Set.empty)
      case _ =>
        // TODO: Can do better (see report)
        updateMember(th, ty)

        // TODO: Is this ok???
        val gadtConstraint = ctx.gadt.asInstanceOf[ProperGadtConstraint]
        var c = gadtConstraint.getConstraint
        val tyVar = typeVarReprs(ecOfTh)
        if !c.contains(tyVar.origin.binder) then
          c = c.add(tyVar.origin.binder, List(tyVar))
        c = c.updateEntry(tyVar.origin, ty)
        gadtConstraint.setConstraint(c)

        (Set.empty, Set.empty, Set.empty)

  def updateMember(th: TH, ty: Type): Unit =
    storedTypes.update(th, ty)

  //////////////////////////////////////////////////////////////////////

  /*
  TODO: Certains points à résoundre:
    - Voir la différence entre GadtCstr et OrdCstrts dans isSubtype
    - Les inégalités entres ECs ne sont pas prise en compte lorsqu'on fait un check isSubtype
      - 2 possibilités:
        - On ajoute des <= et >= entre les ECs et les membres ECs dans GadtConstraint
        - OU on fait notre propre isSubtype
          - De tte façon, il faudra un jour ou l'autre intégrer ces égalités+inégalités dans GadtCstrts/OrderingCstrts
          alors, autant le faire tte de suite?
    - Intégration des connaissances ultérieures (outer OrdCstr/GadtCstrt)
    - Check false plus poussé: par example, si Int et String sont dans la même EC, il y a contradiction
  */

  def simplifyLoop(pat: Type, scrut: Type)(using Context): Boolean =
    val origCstrts = createConstraints(pat, scrut) match
      case Some(cstrts) => cstrts
      case None => return false
    println("CONSTRAINTS ARE "+origCstrts.map((s, t) => i"$s <: $t").mkString(", "))
    val cstrts = mutable.Stack.from(origCstrts)
    while cstrts.nonEmpty do
      val (s, t) = cstrts.pop()
      println(i"DEDUCTION FOR $s <: $t")
      deductionIneq(s, t) match
        case Some(deductions) =>
          println("--> We have: " + deductions.map((a, b) => i"$a <: $b").mkString(", "))
          println("---------------------\n")
          val newCsrtrts = deductions.foldLeft(Set.empty[(Type, Type)]) {
            case (acc, (u, v)) => acc ++ compact(u, v)
          }
          cstrts ++= newCsrtrts
        case None => return false

    true

  // TODO: this fn incorporates a weak form of deductionPathTyped
  def createConstraints(pat: Type, scrut: Type)(using Context): Option[Set[(Type, Type)]] =
    def invariantIntersection(variances: List[Variance], argsL: List[Type], argsR: List[Type]): Option[Set[(Type, Type)]] =
      assert(variances.size == argsL.size)
      assert(argsL.size == argsR.size)
      variances.zip(argsL.zip(argsR)).foldLeft(Option(Set.empty[(Type, Type)])) {
        case (Some(acc), (v, (argL, argR))) if varianceToInt(v) == 0 =>
          deductionIneq(argL, argR).zip(deductionIneq(argR, argL))
            .map((lr, rl) => acc ++ lr ++ rl)
        case (acc, _) => acc
      }

    def upcastIntersection(variances: List[Variance], leftUpcasted: List[Type], argsR: List[Type]): Option[Set[(Type, Type)]] =
      assert(variances.size == argsR.size)
      leftUpcasted.foldLeft(Option(Set.empty[(Type, Type)])) {
        case (Some(acc), AppliedType(_, argsL)) =>
          invariantIntersection(variances, argsL, argsR).map(_ ++ acc)
        case (acc, _) => acc
      }

    ////////////////////////////////////////////////

    pat match
      case AppliedType(tyconPat: TypeRef, _) if tyconPat.symbol.isClass && tyconPat.symbol.is(Final) =>
        return Some(Set((pat, scrut)))
      case tyconPat: TypeRef if tyconPat.symbol.isClass && tyconPat.symbol.is(Final) =>
        return Some(Set((pat, scrut)))
      case _ => ()

    val intersectDNF = disjunctions(AndType.make(pat, scrut, true))
    val inCommon = commonTypes(intersectDNF)
    val pairs = inCommon.flatMap(a => inCommon.flatMap(b => if a == b then None else Some((a, b))))
    pairs.foldLeft(Option(Set.empty[(Type, Type)])) {
      case (Some(acc), (AppliedType(tyconL: TypeRef, argsL), AppliedType(tyconR: TypeRef, argsR))) if tyconL.symbol.isClass && tyconR.symbol.isClass =>
        val clsL: ClassSymbol = tyconL.symbol.asClass
        val clsR: ClassSymbol = tyconR.symbol.asClass
        // TODO: Comp ok ?
        if clsL == clsR then
          val variances = clsL.typeParams.map(_.paramVariance)
          invariantIntersection(variances, argsL, argsR).map(_ ++ acc)
        else if clsL.classDenot.derivesFrom(clsR) then
          // Variance of the right-hand side class, not the left
          val variances = clsR.typeParams.map(_.paramVariance)
          val leftUpcasted = upcastTo(clsL, argsL, clsR)
          upcastIntersection(variances, leftUpcasted, argsR).map(_ ++ acc)
        else
          Some(acc)

      // case (Some(acc), (AppliedType(tyconL: TypeRef, argsL), tyconR: TypeRef)) if tyconL.symbol.isClass && tyconR.symbol.isClass =>

      case (Some(acc), (tyconL: TypeRef, AppliedType(tyconR: TypeRef, argsR))) if tyconL.symbol.isClass && tyconR.symbol.isClass =>
        val clsL: ClassSymbol = tyconL.symbol.asClass
        val clsR: ClassSymbol = tyconR.symbol.asClass

        // TODO: Comp ok ?
        if clsL == clsR then
          // TODO: This case is meaningless, right?
          Some(acc)
        else if clsL.classDenot.derivesFrom(clsR) then
          // Variance of the right-hand side class, not the left
          val variances = clsR.typeParams.map(_.paramVariance)
          val leftUpcasted = upcastTo(clsL, Nil, clsR)
          upcastIntersection(variances, leftUpcasted, argsR).map(_ ++ acc)
        else
          Some(acc)

      // case (Some(acc), (tyconL: TypeRef, tyconR: TypeRef)) if tyconL.symbol.isClass && tyconR.symbol.isClass =>

      case (acc, _) => acc
    }

  def deductionIneq(s: Type, t: Type)(using Context): Option[Set[(Type, Type)]] =
    println(i"DEDUCTION OF $s <: $t")
    //    println(s)
    //    println(t)
    //    println("----")
    (s, t) match
      // TODO: Refinement things

      case (s, t) if s == defn.NothingType || t == defn.AnyType || s == t =>
        Some(Set.empty)

      case (AppliedType(tyconL: TypeRef, argsL), AppliedType(tyconR: TypeRef, argsR)) if tyconL.symbol.isClass && tyconR.symbol.isClass =>
        val clsL: ClassSymbol = tyconL.symbol.asClass
        val clsR: ClassSymbol = tyconR.symbol.asClass
        // TODO: Comp ok ?
        if clsL == clsR then
          val variances = s.typeParams.map(_.paramVariance)
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
          val leftUpcasted = upcastTo(clsL, argsL, clsR)
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
          val leftUpcasted = upcastTo(clsL, argsL, clsR)
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
          val leftUpcasted = upcastTo(clsL, Nil, clsR)
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
          val leftUpcasted = upcastTo(clsL, Nil, clsR)
          // TODO: reduce ~> foldLeft
          // TODO: or should we "never" encounter empty leftUpcasted ?
          deductionIneq(leftUpcasted.reduce(AndType.make(_, _, true)), t)
        else
          None

      case (AppliedType(tyconL: TypeRef, argsL), AppliedType(tyconR: TypeRef, argsR)) =>
        Some(Set((s, t)))

      // TODO: For these two remarks: we need to register bounds on EC creation
      case (s, t: AndType) =>
        deductionIneq(s, t.tp1).zip(deductionIneq(s, t.tp2)).map((a, b) => a ++ b ++ Set((s, t))) // TODO: ++ Set((s, t)) to help a bit for equality like X & Y = Z & W

      case (s: OrType, t) =>
        deductionIneq(s.tp1, t).zip(deductionIneq(s.tp2, t)).map((a, b) => a ++ b ++ Set((s, t))) // TODO: ++ Set((s, t)) to help a bit for equality like X & Y = Z & W

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
        //        println(sBounds)
        //        println(tBounds)
        //        println("DO WE HAVE SAME VARIANCE ? "+(sBounds.map(_._1) == tBounds.map(_._1)))
        //        println("DO WE HAVE SAME PARAM ? "+(sBounds.map(_._2) == tBounds.map(_._2)))
        //        println(sBounds.head._2)
        //        println(tBounds.head._2)
        //        println(sBounds.head._2.equals(tBounds.head._2))
        // TODO
        // TODO
        // TODO
        // TODO
        // TODO
        // FIXME
        // assert(sBounds.corresponds(tBounds) { case ((vl, tyParamL, _), (vr, tyParamR, _)) => vl == vr && tyParamL == tyParamR })
        val tyParams = sBounds.map(_._2)
        if !BSubsumes(tBounds, sBounds) then
          return Some(Set.empty)

        def boundsOfSEntailed = BEntailed(sBounds)
        def noOccurrenceOfTyVars(res: Set[(Type, Type)]): Boolean =
          res.forall((l, r) =>
            tyParams.forall(tyParam => !tyParam.occursIn(l) && !tyParam.occursIn(r)))

        deductionIneq(s.resType, t.resType) match
          case Some(res) if boundsOfSEntailed && noOccurrenceOfTyVars(res) =>
            Some(res)
          case Some(res) =>
            Some(res.map((l, r) => (closeOver(l, sBounds), closeOver(r, tBounds))))
          case None =>
            if boundsOfSEntailed then
              None
            else
              Some(Set.empty)

      case (s: TypeRef, t: TypeRef) if s.symbol.isClass && t.symbol.isClass && !s.symbol.asClass.classDenot.derivesFrom(t.symbol.asClass) =>
        None

      case (s: TypeRef, t: TypeRef) => Some(Set((s, t)))

      // TODO: other cases to consider
      case _ => Some(Set.empty)

  def registerSubtypeEC(a: ECH, b: ECH)(using ctx: Context) =
    val aTyVar = typeVarReprs(a)
    val bTyVar = typeVarReprs(b)
    val gadtCstrt = ctx.gadt.asInstanceOf[ProperGadtConstraint]
    var c = gadtCstrt.getConstraint
    if !c.contains(aTyVar.origin.binder) then
      c = c.add(aTyVar.origin.binder, List(aTyVar)) // TODO: Ok?
    if !c.contains(bTyVar.origin.binder) then
      c = c.add(bTyVar.origin.binder, List(bTyVar)) // TODO: Ok?
    c = c.addLess(aTyVar.origin, bTyVar.origin) // TODO: Ok?
    gadtCstrt.setConstraint(c)

  // TODO: Messy
  def registerEqEC(a: ECH, b: ECH, aTyVar: TypeVar, bTyVar: TypeVar)(using ctx: Context) =
    assert(unionFind.find(a) == unionFind.find(b))
//    val aTyVar = typeVarReprs(a)
//    val bTyVar = typeVarReprs(b)
    val gadtCstrt = ctx.gadt.asInstanceOf[ProperGadtConstraint]
    var c = gadtCstrt.getConstraint
    if !c.contains(aTyVar.origin.binder) then
      c = c.add(aTyVar.origin.binder, List(aTyVar)) // TODO: Ok?
    if !c.contains(bTyVar.origin.binder) then
      c = c.add(bTyVar.origin.binder, List(bTyVar)) // TODO: Ok?

    if unionFind.find(a) == a then
      c = c.unify(aTyVar.origin, bTyVar.origin)
    else
      c = c.unify(bTyVar.origin, aTyVar.origin)

    gadtCstrt.setConstraint(c)

  def tryRegisterSubtypeNamedType(a: Type, b: Type)(using ctx: Context) =
    (a, b) match
      case (a: NamedType, b: NamedType) =>
        val aSym = a.symbol
        val bSym = b.symbol
        if !ctx.gadt.contains(aSym) then
          ctx.gadt.addToConstraint(aSym)
        if !ctx.gadt.contains(bSym) then
          ctx.gadt.addToConstraint(bSym)
        // TODO: This can ultimately fire isSubtype...
        ctx.gadt.addBound(aSym, b, isUpper = true)
        ctx.gadt.addBound(bSym, a, isUpper = false)

      case (a: NamedType, b) =>
        val aSym = a.symbol
        if !ctx.gadt.contains(aSym) then
          ctx.gadt.addToConstraint(aSym)
        // TODO: This can ultimately fire isSubtype...
        ctx.gadt.addBound(aSym, b, isUpper = true)

      case (a, b: NamedType) =>
        val bSym = b.symbol
        if !ctx.gadt.contains(bSym) then
          ctx.gadt.addToConstraint(bSym)
        // TODO: This can ultimately fire isSubtype...
        ctx.gadt.addBound(bSym, a, isUpper = false)

      case _ => ()

  def tryRegisterEqNamedType(a: Type, b: Type)(using ctx: Context) =
    // TODO: No better way?
    tryRegisterSubtypeNamedType(a, b)
    tryRegisterSubtypeNamedType(b, a)

  def compact(s: Type, t: Type)(using ctx: Context): Set[(Type, Type)] =
    val msg = i"COMPACT $s <: $t"
    println(msg)
    println(debugString) // "[X0] =>> F[X0] <: Vector"
    val sGot = TFindOrCreateEC(s, Nil, true, true)
    println(i"TFind FOR $s: $sGot   (${sGot.toString})")
    val sTyVar = sGot.asInstanceOf[TypeVar]
    val sEC = typeVarEC(sTyVar)
    println(i"EC: $sEC")
    println("-------")
    val tGot = TFindOrCreateEC(t, Nil, true, true)
    println(i"TFind FOR $t: $tGot")
    val tTyVar = tGot.asInstanceOf[TypeVar]
    val tEC = typeVarEC(tTyVar)
    println(i"EC: $tEC")

    addIneq(sEC, tEC) match
      case Left(()) =>
        val cstrts = mutable.Set.empty[(Type, Type)]
        val toMerge = mutable.Stack((sEC, tEC))
        while toMerge.nonEmpty do
          val (a, b) = toMerge.pop()
          val aa = unionFind.find(a)
          val bb = unionFind.find(b)
          if aa != bb then
            val typesInA = members(aa).map(storedTypes).toSet
            val typesInB = members(bb).map(storedTypes).toSet
            val tyVarA = typeVarReprs(aa)
            val tyVarB = typeVarReprs(bb)
            val (newCsrts, newToMerge) = merge(aa, bb)

            registerEqEC(aa, bb, tyVarA, tyVarB)
            typesInA.foreach(tA => typesInB.foreach(tB => tryRegisterEqNamedType(tA, tB)))

            cstrts ++= newCsrts
            toMerge ++= newToMerge
        println("==============\n")
        cstrts.toSet
      case Right(cstrts) =>
        println("==============\n")
        registerSubtypeEC(sEC, tEC)
        val typesInS = members(sEC).map(storedTypes).toSet
        val typesInT = members(tEC).map(storedTypes).toSet
        typesInS.foreach(tS => typesInT.foreach(tT => tryRegisterSubtypeNamedType(tS, tT)))

        cstrts

  def addIneq(a: ECH, b: ECH)(using Context): Either[Unit, Set[(Type, Type)]] =
    if !gSub.chain(b, a).isEmpty then
      Left(())
    else if !gSub.chain(a, b).isEmpty then
      Right(Set.empty)
    else
      val lowerWDets = gSub.strictLowerBounds(a).flatMap(weaklyDetsOf)
      val upperWDets = gSub.strictUpperBounds(b).flatMap(weaklyDetsOf)
      gSub.addIneq(a, b)
      Right(lowerWDets.flatMap(l => upperWDets.map(r => (l, r))))

  def merge(a: ECH, b: ECH)(using Context): (Set[(Type, Type)], Set[(ECH, ECH)]) =
    def helper: (Set[(Type, Type)], Set[(ECH, ECH)]) =
      val ab = unionFind.union(a, b)

      val membsA = members(a).toSet
      val membsB = members(b).toSet
      members -= a
      members -= b
      members += ab -> mutable.Set.from(membsA ++ membsB)

      ecOf.mapValuesInPlace {
        case (_, ec) =>
          if ec == a || ec == b then ab
          else ec
      }

      if dets.contains(a) then
        val detA = dets(a)
        dets -= a
        dets -= b
        dets += ab -> detA
      else if dets.contains(a) then
        val detB = dets(b)
        dets -= a
        dets -= b
        dets += ab -> detB

      val tyVarReprA = typeVarReprs(a)
      val tyVarReprB = typeVarReprs(b)
      if ab == a then
        typeVarReprs(b) = tyVarReprA
        typeVarEC(tyVarReprB) = a
      else
        assert(ab == b)
        typeVarReprs(a) = tyVarReprB
        typeVarEC(tyVarReprA) = b

      gSub.merge(a, b, ab)

      // TODO: should but registerEC & co here
      // TODO: should but registerEC & co here
      // TODO: should but registerEC & co here

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

    println(s"MERGING $a WITH $b")
    println(debugString)

    val allCsrts = mutable.Set.empty[(Type, Type)]
    val allToMerge = mutable.Set.empty[(ECH, ECH)]

    gSub.chain(a, b) match
      case Some(chain) if chain.length == 2 =>
        assert(chain == Seq(a, b))
      case Some(chain) =>
        return (Set.empty, chain.zip(chain.tail).toSet)
      case None =>
        gSub.chain(b, a) match
          case Some(chain) if chain.length == 2 =>
            assert(chain == Seq(b, a))
          case Some(chain) =>
            return (Set.empty, chain.zip(chain.tail).toSet)
          case None =>
            // TODO: Need to register smth w.r.t. GadtConstraint ???
            addIneq(a, b) match
              case Right(cstrts) => allCsrts ++= cstrts
              case Left(()) => assert(false)

//    println(s"DET STATUS: ${(dets.contains(a), dets.contains(b))}")
//    println(debugString)
//    println(typeVarReprs)
    // TODO: aussi pour mettre dans gadt cstrts?

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

    val (cstrts, toMerge) = helper
    allCsrts ++= cstrts
    allToMerge ++= toMerge
    println("MERGE FINISHED:")
    println(debugString)
    println("NEW CSTRST: "+allCsrts)
    println("NEW TO MERGE: "+toMerge)
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
      case ECTypeVar(otherEC) if unionFind.find(otherEC) == unionFind.find(ec) =>
        to
      case AppliedECTypeVar(otherEC, args) if unionFind.find(otherEC) == unionFind.find(ec) =>
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

  // TODO: Should return a type of the following:
  //  -[a]
  //  -[a][args]
  //  -[X >: ... <: ...] =>> [a][args]
  //  All of these can be transformed to plain Type accordingly
  def TFindOrCreateEC(oldT: Type,
    bounds: BoundsInfo,
    inHead: Boolean,
    create: Boolean)(using ctx: Context): Type =
    val t = oldT match
      case t: TypeRef if !t.hasSimpleKind =>
        t.EtaExpand(t.typeParams)
      case _ => oldT

    t match
      case t: TypeParamRef =>
        // TODO: Même si higher-kinded ? ~> il semblerait que oui
        t

      case AppliedType(tycon, args) =>
        val argsRec = args.map(a => TFindOrCreateEC(a, bounds, false, create))
        tycon match
          case tv@ECTypeVar(_) =>
            AppliedType(tv, argsRec)
          case _: TypeParamRef =>
            // HK type bounded in an enclosing HK
            AppliedType(tycon, argsRec)
          case tycon: TypeRef =>
            if tycon.symbol.isClass && !bounds.isEmpty then AppliedType(tycon, argsRec)
            else TECFindOrCreateEC(AppliedType(tycon, argsRec), bounds, create)
          case _ =>
            ???

      case t: AndOrType =>
        val dnfDisjs = disjunctions(t)
        val disjsRec = mutable.Set.empty[Set[Type]]
        for (disj <- dnfDisjs) {
          val conjsRec = mutable.Set.empty[Type]
          for (conj <- disj) {
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
        val dnfRec = disjunctionsToType(disjsRec.toSet)
        val isDNF = !(disjsRec.size == 1 && disjsRec.head.size == 1)
        if isDNF && inHead && !bounds.isEmpty then // TODO: !bounds.isEmpty -> no termref appearing in dnf
          dnfRec
        else
          TECFindOrCreateEC(dnfRec, bounds, create)

      case tv@ECTypeVar(_) => tv

      // TODO: TypeVar ok ?
      case t: (TypeRef | TypeVar) if t.hasSimpleKind =>
        TECFindOrCreateEC(t, bounds, create)

      // TODO: TypeVar ok ?
      case t: (TypeRef | TypeVar) =>
        TFindOrCreateEC(t.EtaExpand(t.typeParams), bounds, inHead, create)

      case hk: HKTypeLambda =>
        val hkBoundsInfo = boundsInfoOf(hk)
//        println("MATCHED HKTYPELAMBAD")
        val hkBoundsRec = BFindOrCreateEC(hkBoundsInfo, bounds, inHead, create)
//        println("hkBoundsRec: "+hkBoundsRec)

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
    val boundsTmp = enclosingBounds ++ hkBounds.map {
      case (v, tyParam, _) => (v, tyParam, TypeBounds.upper(topOfKind(tyParam)))
    }
    hkBounds.map { case (v, tyName, tb) =>
      val loRec = TFindOrCreateEC(tb.lo, boundsTmp, true, create)
      val hiRec = TFindOrCreateEC(tb.hi, boundsTmp, true, create)
      (v, tyName, TypeBounds(loRec, hiRec))
    }


  def TECFindOrCreateEC(
    t: Type,
    bounds: BoundsInfo,
    create: Boolean)(using Context): Type =
    t match
      case t if t.hasSimpleKind =>
        if notAppearingIn(bounds.map(_._2).toSet, t) then
          val candidatesIt = allMembers.iterator
          while (candidatesIt.hasNext) {
            val h = candidatesIt.next()
            storedTypes.get(h) match
              case Some(s) if s.hasSimpleKind => // && TECEquiv(...)
                if TECEquiv(t, s) then
                  return typeVarReprs(ecOf(h))
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
        if notAppearingIn(bounds.map(_._2).toSet, t) then
          val candidatesIt = allMembers.iterator
          while (candidatesIt.hasNext) {
            val h = candidatesIt.next()
            storedTypes.get(h) match
              case Some(hkCand: HKTypeLambda) if hk.hasSameKindAs(hkCand)
                && TECEquiv(hk.resType, hkCand.resType)
                && BECEquiv(boundsInfoOf(hk), boundsInfoOf(hkCand)) =>
                // TODO: Explain why we do not eta-expand...
                return typeVarReprs(ecOf(h))
//                return tyVar.EtaExpand(tyVar.typeParams)
              case _ => ()
          }
        if create then
          TECCreate(t, bounds)
        else
          throw ECNotFound()

      case _ =>
        ???

  def TECCreate(t: Type, bounds: BoundsInfo)(using ctx: Context): Type =
    val newEC = unionFind.add()
    println(i"CREATING AN EC FOR $t WITH EC [$newEC]")
    println(debugString)
    val (typeToStore, tyVarRepr, typeToReturn) = {
      t match
        case t if t.hasSimpleKind =>
          if notAppearingIn(bounds.map(_._2).toSet, t) then
            val tyVarRepr = newTypeVar(TypeBounds.empty)
            (t, tyVarRepr, tyVarRepr)
          else
            val tyVarRepr = newHKTypeVarWithBounds(bounds)
            // - For typeToStore, we need to create [vX <| BX] =>> T
            //   ~~> We need to substitute the typeparamref with new syntectic names
            // - For returnedType, we need to create [newEC][X]  <--- the "X" here are the X in bounds, not of the HK
            (closeOver(t, bounds), tyVarRepr, AppliedType(tyVarRepr, bounds.map(_._2)))

        case hk: HKTypeLambda =>
          val hkBoundsInfo = boundsInfoOf(hk)
          if notAppearingIn(bounds.map(_._2).toSet, hk) then
            val tyVarRepr = newHKTypeVarWithBounds(hkBoundsInfo)
            (hk, tyVarRepr, tyVarRepr)
          else
            // TODO: Verify this thing
            val newHKBoundsInfo = bounds ++ hkBoundsInfo
            val tyVarRepr = newHKTypeVarWithBounds(newHKBoundsInfo)
            (closeOver(hk.resType, newHKBoundsInfo),
              tyVarRepr,
              closeOver(AppliedType(tyVarRepr, newHKBoundsInfo.map(_._2)), hkBoundsInfo))

        case _ => ???
    }

    val storedTypeTH = TH.fromInt(thCounter)
    thCounter += 1
    members += newEC -> mutable.Set(storedTypeTH)
    ecOf += storedTypeTH -> newEC
    storedTypes += storedTypeTH -> typeToStore
    typeVarReprs += newEC -> tyVarRepr
    typeVarEC += tyVarRepr -> newEC

    if isDet(typeToStore) then
      // TODO: Is this ok???
      val gadtConstraint = ctx.gadt.asInstanceOf[ProperGadtConstraint]
      val c = gadtConstraint.getConstraint
        .add(tyVarRepr.origin.binder, List(tyVarRepr))
        .updateEntry(tyVarRepr.origin, typeToStore)
      gadtConstraint.setConstraint(c)

      dets += newEC -> storedTypeTH

    println(i"EC CREATED: returning $typeToReturn")
    println(debugString)
    println("------------------\n")
    typeToReturn

  // TODO: Ensure of simple kind
  def TECTryFindApplied(t: Type,
    bounds: BoundsInfo)(using Context): Option[Type] =
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
                    val ecTyVar = typeVarReprs(ecOf(h))
                    val applied = AppliedType(ecTyVar, substImgOrdered)

                    if notAppearingIn(bounds.map(_._2).toSet, t) && noTypeParams(applied) then
                      TECTryFindECOfApplied(ecOf(h), substImgOrdered) match
                        case Some(ec) => return Some(typeVarReprs(ec))
                        case None => ()
                    if notAppearingIn(bounds.map(_._2).toSet, t) then
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
        case AppliedECTypeVar(candEC, candArgs)
        if unionFind.find(candEC) == unionFind.find(tyconEC) &&
          candArgs.corresponds(args)(TECEquiv) =>
          return Some(ecOf(h))
        case _ => ()
    }
    None


  //////////////////////////////////////////////////////////////////////////////////

  // TODO: Good enough ?
  // TODO: Il semblerait que cela ne marche pas bien en présence de dnf...
  def TECEquiv(t: Type, s: Type)(using Context): Boolean =
    TypeComparer.isSameTypeWhenFrozen(t, s)

  // TODO: Marche assui avec refn on dirait ?
  def BSubsumes(l: BoundsInfo, r: BoundsInfo)(using Context): Boolean =
    assert(l.corresponds(r) { case ((vl, tl, _), (vr, tr, _)) => vl == vr && tl.hasSameKindAs(tr) })

    val newParams: List[TypeVar] = l.map((_, ty, _) => newTypeVarOfSameKind(ty))
    val map = l.map(_._2).zip(newParams).toMap ++ r.map(_._2).zip(newParams).toMap
    val typeMap = new TypeMap {
      override def apply(tp: Type): Type = tp match
        case tp: TypeParamRef =>
          map.getOrElse(tp, mapOver(tp))
        case t => mapOver(t)
    }
    l.map(_._3).zip(r.map(_._3)).forall {
      case (TypeBounds(lo1, hi1), TypeBounds(lo2, hi2)) =>
        TypeComparer.isSubTypeWhenFrozen(typeMap(lo2), typeMap(lo1)) &&
          TypeComparer.isSubTypeWhenFrozen(typeMap(hi2), typeMap(hi1))
    }

  // TODO: Marche aussi avec refn on dirait ?
  def BEntailed(bnds: BoundsInfo)(using Context): Boolean =
    bnds.forall { case (_, _, TypeBounds(lo, hi)) => TypeComparer.isSubTypeWhenFrozen(lo, hi) }

  def BECEquiv(l: BoundsInfo, r: BoundsInfo)(using Context): Boolean =
    assert(l.corresponds(r) { case ((_, tl, _), (_, tr, _)) => tl.hasSameKindAs(tr) })

    def isEquiv =
      val newParams: List[TypeVar] = l.map((_, ty, _) => newTypeVarOfSameKind(ty))
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

  //////////////////////////////////////////////////////////////////////

  def TECTryMatch(xs: Set[TypeParamRef], t: Type, s: Type)(using Context): Option[Map[TypeParamRef, Type]] =
    // assert(ftv(s).intersect(xs).isEmpty)
    assert(notAppearingIn(xs, s))
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

      case (AppliedECTypeVar(ec1, args1), AppliedECTypeVar(ec2, args2)) if unionFind.find(ec1) == unionFind.find(ec2) =>
        TECTryMatchVec(xs, args1, args2)

      // TODO: tycon comp. a bit too restrictive ?
      case (AppliedType(tycon1, args1), AppliedType(tycon2, args2)) if tycon1 == tycon2 =>
        TECTryMatchVec(xs, args1, args2)

      case (hk1: HKTypeLambda, hk2: HKTypeLambda) =>
        assert(hk1.paramNames.size == hk2.paramNames.size)
        // TODO: Ok w.r.t. tyvar that are not "fresh" and that hk1 and hk2 var are not the same ?
        val hk1Vars = hk1.paramRefs.toSet
        val hk2Vars = hk2.paramRefs.toSet
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

  def allTyVarsOf(ec: ECH): Set[TypeVar] =
    typeVarEC.filter((_, cand) => cand == ec).map(_._1).toSet

  def debugString(using Context): String =
    if members.isEmpty then
      return "(empty K)"

    val ecsContent =
        members.foldLeft(Seq.empty[String]) {
          case (acc, (ec, membs)) =>
            val membsSorted = membs.toSeq.sortBy(_.toInt)
            val tys = membsSorted.map(th => storedTypes(th).show).mkString(", ")
            val tyVars = allTyVarsOf(ec).map(_.show).mkString(",")
            acc :+ s"""$ec: {$tys}   (THs: {${membsSorted.mkString(",")}},  TyVars: {$tyVars})"""
        }.mkString("\n")
//    val ecsBelonging =
//      ecOf.map((th, ec) => s"$th -> [$ec]").mkString(", ")
//    val tyRepr = typeVarReprs.map((ec, tyVar) => i"[$ec] -> $tyVar").mkString(", ")
    ecsContent ++ "\n" ++ gSub.debugString



case class TryMatchFail() extends Exception

case class ECNotFound() extends Exception
