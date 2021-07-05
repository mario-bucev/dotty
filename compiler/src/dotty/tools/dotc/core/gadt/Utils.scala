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
    val hkParamRefs = (0 until hk.paramNames.size).map(hk.paramRefs)
    hkVariance.zip(hkParamRefs.zip(hk.paramInfos)).map { case (a, (b, c)) => (a, b, c) }

  def toDNF(t: Type)(using Context): DNF =
    t match
      case AndType(lhs, rhs) =>
        val lhsDNF = toDNF(lhs)
        val rhsDNF = toDNF(rhs)
        DNF(lhsDNF.disjunctions.flatMap(lConjs => rhsDNF.disjunctions.map(rConjs => lConjs ++ rConjs)))
      case OrType(lhs, rhs) =>
        val lhsDNF = toDNF(lhs)
        val rhsDNF = toDNF(rhs)
        DNF(lhsDNF.disjunctions ++ rhsDNF.disjunctions)
      case t =>
        DNF(Set(Set(t)))

  def unordPairs[A](s: Set[A]): Set[(A, A)] =
    s.flatMap(a => s.flatMap(b => if a == b then None else Some((a, b))))

  def closeOver(t: Type, bounds: BoundsInfo)(using Context): Type =
    val newParams = HKTypeLambda.syntheticParamNames(bounds.length)
    val map = (hk: HKTypeLambda) => new TypeMap {
      override def apply(tp: Type): Type = tp match
        case tp: TypeParamRef =>
          bounds.indexWhere((_, candidate, _) => candidate == tp) match
            case i if i >= 0 => hk.paramRefs(i)
            case _ => mapOver(tp)
        case t => mapOver(t)
    }
    HKTypeLambda(newParams, bounds.map(_._1))(
      hk => bounds.map { case (_, _, TypeBounds(lo, hi)) => TypeBounds(map(hk)(lo), map(hk)(hi)) },
      hk => map(hk)(t))

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
    val result = typer.ProtoTypes.newTypeVar(TypeBounds.upper(topOfKind(targetKind)))
    assert(result.hasSameKindAs(targetKind))
    result

  def newHKTypeVarWithBounds(bounds: BoundsInfo)(using Context): TypeVar =

    ???

  /*
  // TODO: Copy/paste of closeOver
  def alphaRename(hk: HKTypeLambda)(using Context): (HKTypeLambda, TypeMap) =
    val boundsInfo = boundsInfoOf(hk)
    // TODO: gen fresh names ???
    val newParams = List.fill(boundsInfo.size)(DepParamName.fresh().toTypeName)  // HKTypeLambda.syntheticParamNames(bounds.length)
    val map = (newHK: HKTypeLambda) => new TypeMap {
      override def apply(tp: Type): Type = tp match
        case tp: TypeParamRef =>
          boundsInfo.indexWhere((_, candidate, _) => candidate == tp) match
            case i if i >= 0 => newHK.paramRefs(i)
            case _ => mapOver(tp)
        case t => mapOver(t)
    }

    val newHK = HKTypeLambda(newParams, boundsInfo.map(_._1))(
      newHK => boundsInfo.map { case (_, _, TypeBounds(lo, hi)) => TypeBounds(map(newHK)(lo), map(newHK)(hi)) },
      newHK => map(newHK)(hk.resType))
    (newHK, map(newHK))
  */

  // TODO: ...
  def ftv(t: Type)(using Context): Set[TypeParamRef] =
    t match
      case t: TypeParamRef => Set(t)
      case AppliedType(tycon, args) =>
        ftv(tycon) ++ args.flatMap(ftv)
      case hk: HKTypeLambda =>
        val hkParamRefs = (0 until hk.paramNames.size).map(hk.paramRefs).toSet
        (hk.paramInfos.flatMap(ftv).toSet ++ ftv(hk.resType)) -- hkParamRefs
      case t: AndOrType =>
        ftv(t.tp1) ++ ftv(t.tp2)
      case t: TypeProxy =>
        ftv(t.underlying)
      //      case t: TypeBounds =>
      //        ftv(t.lo) ++ ftv(t.hi)
      // TODO: There are other cases to consider
      case _ => Set.empty

