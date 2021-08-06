package dotty.tools
package dotc
package core

import Variances.*
import UnionFind.*
import Types.*
import Names.*
import Decorators.*
import Contexts.*
import Symbols.*
import NameKinds.DepParamName

import scala.collection.mutable

object GadtUtils:

  type BoundsInfo = List[(Variance, TypeParamRef, TypeBounds)]

  def isSubtypeInFrozenConstraint(s: Type, t: Type, cstrt: Constraint)(using ctx: Context): Boolean =
    // TODO: Not sure if we are supposed to do that...
    val savedCstrt = ctx.typerState.constraint
    try
      ctx.typerState.constraint = cstrt
      TypeComparer.isSubTypeWhenFrozen(s, t)
    finally
      ctx.typerState.constraint = savedCstrt

  def isSameInFrozenConstraint(s: Type, t: Type, cstrt: Constraint)(using ctx: Context): Boolean =
    // TODO: Not sure if we are supposed to do that...
    val savedCstrt = ctx.typerState.constraint
    try
      ctx.typerState.constraint = cstrt
      TypeComparer.isSameTypeWhenFrozen(s, t)
    finally
      ctx.typerState.constraint = savedCstrt

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
    // TODO: do not foldLeft with bot/top
    disjs.foldLeft(defn.NothingType: Type)((acc, conjs) =>
      // TODO: Soft = ???
      OrType.make(conjs.foldLeft(defn.AnyType: Type)((acc2, ty) => AndType.make(ty, acc2)), acc, false))

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

  def etaExpandIfNeeded(t: Type)(using Context): Type =
    if t.hasSimpleKind then t
    else
      // TODO: ...
      val expanded = t.EtaExpand(t.typeParams).asInstanceOf[HKTypeLambda]
      alphaRename(expanded, expanded)._1

  def constraintsFromTyconBounds(tycon: TypeRef, appliedArgs: List[Type])(using Context): Set[(Type, Type)] =
    assert(appliedArgs.nonEmpty)
    val params = tycon.typeParams
    assert(params.length == appliedArgs.length)
    // We will need to substitute the type parameters with their corresponding appliedArgs.
    // The TypeParamInfo contained in params depends on the nature of tycon.
    // If tycon refers to a class, the params are all Symbols
    // Otherwise, they are all LambdaParam
    val (paramSyms, paramLambda) = params.partitionMap {
      case s: Symbol => Left(s)
      case lp: LambdaParam => Right(lp)
    }
    assert(paramSyms.length == appliedArgs.length ^ paramLambda.length == appliedArgs.length)
    // Furthermore, if paramLambda is not empty, the binding of all LambdaParam refer to the same TypeLambda
    assert(paramLambda.map(_.tl).toSet.size <= 1)

    def substParams(t: Type): Type =
      if params.nonEmpty then
        t.subst(paramSyms, appliedArgs)
      else
        t.substParams(paramLambda.head.tl, appliedArgs)

    params.zip(appliedArgs).foldLeft(Set.empty[(Type, Type)]) {
      case (acc, (param, arg)) =>
        param.paramInfo match
          case TypeBounds(lo, hi) =>
            val loSubsted = substParams(lo)
            val hiSubsted = substParams(hi)
            acc ++ Set((loSubsted, arg), (arg, hiSubsted))
          case _ => acc
    }

  // TODO: What does a "Nil" implies?
  def upcastTo(child: ClassSymbol, args: List[Type], parentClsSym: ClassSymbol)(using Context): (List[Type], Set[(Type, Type)]) =
    assert(child.classDenot.derivesFrom(parentClsSym))
    val parentTypeRef = parentClsSym.classDenot.typeRef

    def helper(candidate: Type): (List[Type], Set[(Type, Type)]) =
      val tyconCandidate = candidate match
        case t: TypeRef => t
        case AppliedType(t: TypeRef, _) => t
        case _ => return (Nil, Set.empty)

      // TODO: Is this even correct ???
      if tyconCandidate == parentTypeRef then
        val substed = candidate.subst(child.classDenot.typeParams, args)
        (List(substed), constraintsFromTyconBounds(tyconCandidate, substed.argInfos))
      else if tyconCandidate.symbol.isClass then
        val candClass = tyconCandidate.symbol.asClass
        if candClass.classDenot.derivesFrom(parentClsSym) then
          val substed = candidate.subst(child.classDenot.typeParams, args)
          upcastTo(candClass, substed.argInfos, parentClsSym)
        else
          (Nil, Set.empty)
      else
        (Nil, Set.empty)

    val childBoundsCstrts = constraintsFromTyconBounds(child.typeRef, args)
    if child == parentClsSym then
      (List(AppliedType(child.typeRef, args)), childBoundsCstrts)
    else
      val allParents = child.classDenot.classInfo.parents
      allParents.foldLeft((List.empty[Type], childBoundsCstrts)) {
        case ((accUpcasts, accBoundsCstrts), parentCandidate) =>
          val (newUpcast, newBoundsCstrts) = helper(parentCandidate)
          (accUpcasts ++ newUpcast, accBoundsCstrts ++ newBoundsCstrts)
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

  def unconstrainedTypeVar(targetKind: Type)(using Context): TypeVar =
    val poly = PolyType(List(DepParamName.fresh(EmptyTermName.toTypeName).toTypeName), List(TypeBounds.upper(topOfKind(targetKind))), defn.AnyType)
    val result = TypeVar(poly.paramRefs.head, creatorState = null)
    assert(result.hasSameKindAs(targetKind))
    result

  def unconstrainedTypeVar(targetKind: List[Type])(using Context): TypeVar =
    val hkBound = HKTypeLambda(HKTypeLambda.syntheticParamNames(targetKind.length), targetKind.map(TypeBounds.upper compose topOfKind), defn.AnyType)
    // TODO: Will we get targetKind => * as kind or will we get a thing that is "off by one" ?
    unconstrainedTypeVar(hkBound)

  /*
  // TODO: To be replaced/removed
  def newTypeVarOfSameKind(targetKind: Type)(using Context): TypeVar =
    val result = unconstrainedTypeVar(TypeBounds.upper(topOfKind(targetKind)))
    assert(result.hasSameKindAs(targetKind))
    result

  // TODO: To be replaced/removed
  def newHKTypeVarWithBounds(bounds: BoundsInfo)(using Context): TypeVar =
    val hkBound = HKTypeLambda(HKTypeLambda.syntheticParamNames(bounds.length), bounds.map(_._1))(
      hk => bounds.map {
        case (_, tyParam, TypeBounds(lo, hi)) =>
          // FIXME
          // TODO: This is almost certainly wrong, because "bounds" can be composed of many enclosing HK,
          //  as such, the subst won't do what we expect
          TypeBounds(lo.subst(tyParam.binder, hk), hi.subst(tyParam.binder, hk))
      },
      _ => defn.AnyType // TODO: Ok ?
    )
    unconstrainedTypeVar(TypeBounds.upper(hkBound))
  */

  // TODO: There are surely better way to do that
  def alphaRename(l: HKTypeLambda, r: HKTypeLambda)(using ctx: Context): (HKTypeLambda, HKTypeLambda) =
    val boundsInfoL = boundsInfoOf(l)
    val boundsInfoR = boundsInfoOf(r)
    // TODO: It seems we can mix lambdas with different isDeclaredVarianceLambda...
    assert(boundsInfoL.corresponds(boundsInfoR) { case ((vl, tl, _), (vr, tr, _)) => /*vl == vr && */ tl.hasSameKindAs(tr) })

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
    !t.existsPart {
      case x: TypeParamRef => xs.contains(x)
      case _ => false
    }

  def noTypeParams(t: Type)(using Context): Boolean =
    t.forallParts {
      case x: TypeParamRef => false
      case _ => true
    }

  // TODO: Say this is incorrect for structural subtyping
  def approxDisj(c1: Option[Set[(Type, Type)]], c2: Option[Set[(Type, Type)]])(using Context): Option[Set[(Type, Type)]] =
    (c1, c2) match
      case (Some(c1), Some(c2)) =>
        val allTypesC1 = c1.flatMap((s, t) => Set(s, t))
        val allTypesC2 = c2.flatMap((s, t) => Set(s, t))
        // Map[Type, Set[Type]]
        val lowerC1 = allTypesC1.map(t => t -> c1.filter((lo, s) => s == t).map(_._1)).toMap
        val lowerC2 = allTypesC2.map(t => t -> c2.filter((lo, s) => s == t).map(_._1)).toMap
        val upperC1 = allTypesC1.map(t => t -> c1.filter((s, hi) => s == t).map(_._2)).toMap
        val upperC2 = allTypesC2.map(t => t -> c2.filter((s, hi) => s == t).map(_._2)).toMap
        Some((allTypesC1 ++ allTypesC2).foldLeft(Set.empty[(Type, Type)]) {
          case (acc, t) =>
            // TODO: Soft = ???
            val combinedLo: Option[(Type, Type)] = lowerC1.get(t).zip(lowerC2.get(t))
              // TODO: makeHk uses liftIfHk that is in a TypeComparer...
              .flatMap((ls1, ls2) => (ls1 ++ ls2).reduceOption(AndType.makeHk(_, _)))
              .map(lo => (lo, t))
            val combinedHi: Option[(Type, Type)] = upperC1.get(t).zip(upperC2.get(t))
              // TODO: makeHk uses liftIfHk that is in a TypeComparer...
              .flatMap((hs1, hs2) => (hs1 ++ hs2).reduceOption(OrType.makeHk(_, _)))
              .map(hi => (t, hi))
            acc ++ Set(combinedLo, combinedHi).flatten
        })
      case (Some(c1), None) => Some(c1)
      case (None, Some(c2)) => Some(c2)
      case (None, None) => None

  def clonedBag[A, B](m: mutable.Map[A, mutable.Set[B]]): mutable.Map[A, mutable.Set[B]] =
    val res = mutable.Map.empty[A, mutable.Set[B]]
    m.foreach((a, bs) => res += a -> bs.clone)
    res
