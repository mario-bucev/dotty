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

object Utils:

  type BoundsInfo = List[(Variance, TypeParamRef, TypeBounds)]

  def boundsInfoOf(hk: HKTypeLambda): BoundsInfo =
    val hkVariance =
      if hk.declaredVariances == Nil then
        List.fill(hk.paramNames.size)(Variances.varianceFromInt(1))
      else hk.declaredVariances
    hkVariance.zip(hk.paramRefs.zip(hk.paramInfos)).map { case (a, (b, c)) => (a, b, c) }

  def toDNF(t: Type)(using Context): Type =
    disjunctionsToType(disjunctions(t))

  def disjunctionsToType(disjs: Set[Set[Type]])(using Context): Type =
    assert(disjs.map(_.size).sum >= 1)
    ???

  def disjunctions(t: Type): Set[Set[Type]] =
    t match
      case AndType(lhs, rhs) =>
        val lhsDNF = disjunctions(lhs)
        val rhsDNF = disjunctions(rhs)
        lhsDNF.flatMap(lConjs => rhsDNF.map(rConjs => lConjs ++ rConjs))
      case OrType(lhs, rhs) =>
        val lhsDNF = disjunctions(lhs)
        val rhsDNF = disjunctions(rhs)
        lhsDNF ++ rhsDNF
      case t =>
        Set(Set(t))

  def commonTypes(disjs: Set[Set[Type]]): Set[Type] =
    disjs.reduce(_.intersect(_))

  def isDet(t: Type)(using Context): Boolean =
    t match
      case t: AndOrType =>
        val disjsSet = disjunctions(t)
        if !disjsSet.forall(_.forall(isDet)) then
          return false
        val disjs = disjsSet.map(conj => conj.reduce(AndType.make(_, _)))
        def noSubDisjs = unordPairs(disjs).forall((disj1, disj2) =>
          TypeComparer.isSubTypeWhenFrozen(disj1, disj2) &&
            TypeComparer.isSubTypeWhenFrozen(disj2, disj1))
        def noSubConjs = disjsSet.forall(conj =>
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

  def isWeaklyDet(t: Type)(using Context): Boolean =
    t match
      case t: AndOrType =>
        disjunctions(t).forall(_.forall(isWeaklyDet))
      case AppliedType(tycon: TypeRef, _) if tycon.symbol.isClass =>
        true
      case t: TypeRef if t.symbol.isClass =>
        true
      case hk: HKTypeLambda =>
        isWeaklyDet(hk.resType)
      case _ =>
        false

  def unordPairs[A](s: Set[A]): Set[(A, A)] =
    if s.isEmpty || s.size == 1 then Set.empty
    else
      s.map(a => s.flatMap(b => if a == b then Set.empty else Set(a, b)))
        .map(pair => (pair.head, pair.last))

  def closeOver(t: Type, bounds: BoundsInfo)(using Context): Type =
    val newParams = HKTypeLambda.syntheticParamNames(bounds.length)
    val map = (hk: HKTypeLambda) => new TypeMap {
      override def apply(tp: Type): Type = tp match
        case tp: TypeParamRef =>
          // TODO: Ok ?
          bounds.indexWhere((_, candidate, _) => candidate == tp) match
            case i if i >= 0 => hk.paramRefs(i)
            case _ => mapOver(tp)
        case t => mapOver(t)
    }
    HKTypeLambda(newParams, bounds.map(_._1))(
      hk => bounds.map { case (_, _, TypeBounds(lo, hi)) => TypeBounds(map(hk)(lo), map(hk)(hi)) },
      hk => map(hk)(t))

  // TODO: What does a "Nil" implies?
  def upcastTo(child: ClassSymbol, args: List[Type], parentClsSym: ClassSymbol)(using Context): List[Type] =
    val parentTypeRef = parentClsSym.classDenot.typeRef

    def helper(candidate: TypeRef | AppliedType): List[Type] =
      val tyconCandidate = candidate match
        case t: TypeRef => t
        case AppliedType(t: TypeRef, _) => t
        case _ => assert(false)

      if tyconCandidate == parentTypeRef then
        candidate.subst(child.classDenot.typeParams, args) :: Nil
      else if tyconCandidate.symbol.isClass then
        val candClass = tyconCandidate.symbol.asClass
        if candClass.classDenot.derivesFrom(parentClsSym) then
          candidate.subst(child.classDenot.typeParams, args) match
            case AppliedType(_, substedArgs) =>
              upcastTo(candClass, substedArgs, parentClsSym)
            case _ =>
              upcastTo(candClass, Nil, parentClsSym)
        else
          Nil
      else
        Nil

    assert(child.classDenot.derivesFrom(parentClsSym))
    val allParents = child.classDenot.classInfo.parents
    allParents.flatMap {
      case cand: TypeRef => helper(cand)
      case cand@AppliedType(_: TypeRef, _) => helper(cand)
      case _ => Nil
    }

  def topOfKind(targetKind: Type)(using Context): Type =
    assert(!targetKind.isAnyKind)
    if targetKind.hasSimpleKind then
      defn.AnyType
    else
      assert(targetKind.hkResult != NoType)
      val topForRes = topOfKind(targetKind.hkResult)
      val topForParams = targetKind.typeParams
        .map(tyParamInfo => topOfKind(tyParamInfo.paramInfo))
      val variances = targetKind.typeParams.map(_.paramVariance)
      HKTypeLambda(HKTypeLambda.syntheticParamNames(topForParams.size), variances)
        (_ => topForParams.map(TypeBounds.upper), _ => topForRes)

  def newTypeVarOfSameKind(targetKind: Type)(using Context): TypeVar =
    val result = newTypeVar(TypeBounds.upper(topOfKind(targetKind)))
    assert(result.hasSameKindAs(targetKind))
    result

  def newHKTypeVarWithBounds(bounds: Utils.BoundsInfo)(using Context): TypeVar =
    val hkBound = HKTypeLambda(HKTypeLambda.syntheticParamNames(bounds.length), bounds.map(_._1))(
      hk => bounds.map {
        case (_, tyParam, TypeBounds(lo, hi)) =>
          // TODO: Ok?
          TypeBounds(lo.subst(tyParam.binder, hk), hi.subst(tyParam.binder, hk))
      },
      _ => defn.AnyType // TODO: Ok ?
    )
    newTypeVar(TypeBounds.upper(hkBound))

  def alphaRename(l: HKTypeLambda, r: HKTypeLambda)(using Context): (HKTypeLambda, HKTypeLambda) =
    val boundsInfoL = boundsInfoOf(l)
    val boundsInfoR = boundsInfoOf(r)
    assert(boundsInfoL.corresponds(boundsInfoR) { case ((vl, tl, _), (vr, tr, _)) => vl == vr && tl.hasSameKindAs(tr) })

    val typeMap = (boundsInfo: BoundsInfo, newHK: HKTypeLambda) => new TypeMap {
      override def apply(tp: Type): Type = tp match
        case tp: TypeParamRef =>
          boundsInfo.indexWhere((_, candidate, _) => candidate == tp) match
            case i if i >= 0 => newHK.paramRefs(i)
            case _ => mapOver(tp)
        case t => mapOver(t)
    }

    // newNames outside, to be sure that they are the same for newHKL and newHKR
    val newNames = HKTypeLambda.syntheticParamNames(boundsInfoL.size)
    val variances = boundsInfoL.map(_._1)
    def createNewHK(oldHK: HKTypeLambda, boundsInfo: BoundsInfo): HKTypeLambda =
      HKTypeLambda(newNames, variances)(
        newHK => boundsInfo.map {
          case (_, _, TypeBounds(lo, hi)) =>
            TypeBounds(typeMap(boundsInfo, newHK)(lo), typeMap(boundsInfo, newHK)(hi))
        },
        newHK => typeMap(boundsInfo, newHK)(oldHK.resType))

    (createNewHK(l, boundsInfoL), createNewHK(r, boundsInfoR))

  def orderedSubst(hkParams: List[TypeParamRef], subst: Map[TypeParamRef, Type])(using Context): List[Type] =
    val substExt: Map[TypeParamRef, Type] = subst ++ (hkParams.toSet -- subst.keySet).map(x => x -> topOfKind(x))
    substExt.toList.sortBy((tyParam, _) => hkParams.indexOf(tyParam)).map(_._2)

  def notAppearingIn(xs: Set[TypeParamRef], t: Type)(using Context): Boolean =
    // ftv(t).intersect(xs).isEmpty
    !t.existsPart {
      case x: TypeParamRef => xs.contains(x)
      case _ => false
    }

  def noTypeParams(t: Type)(using Context): Boolean =
    t.forallParts {
      case x: TypeParamRef => false
      case _ => true
    }
  /*
  // TODO: ...
  def ftv(t: Type)(using Context): Set[TypeParamRef] =
    t match
      case t: TypeParamRef => Set(t)
      case AppliedType(tycon, args) =>
        ftv(tycon) ++ args.flatMap(ftv)
      case hk: HKTypeLambda =>
        (hk.paramInfos.flatMap(ftv).toSet ++ ftv(hk.resType)) -- hk.paramRefs.toSet
      case t: AndOrType =>
        ftv(t.tp1) ++ ftv(t.tp2)
      case t: TypeProxy =>
        ftv(t.underlying)
      //      case t: TypeBounds =>
      //        ftv(t.lo) ++ ftv(t.hi)
      // TODO: There are other cases to consider
      case _ => Set.empty
  */
