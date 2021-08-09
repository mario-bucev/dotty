package dotty.tools
package dotc
package core

import Decorators._
import Contexts._
import Types._
import Symbols._
import util.SimpleIdentityMap
import collection.mutable
import printing._

import scala.annotation.internal.sharable

/** Represents GADT constraints currently in scope */
sealed abstract class GadtConstraint extends Showable {
  /** Immediate bounds of `sym`. Does not contain lower/upper symbols (see [[fullBounds]]). */
  def bounds(sym: Symbol)(using Context): TypeBounds

  /** Full bounds of `sym`, including TypeRefs to other lower/upper symbols.
   *
   * @note this performs subtype checks between ordered symbols.
   *       Using this in isSubType can lead to infinite recursion. Consider `bounds` instead.
   */
  def fullBounds(sym: Symbol)(using Context): TypeBounds

  /** Is `sym1` ordered to be less than `sym2`? */
  def isLess(sym1: Symbol, sym2: Symbol)(using Context): Boolean

  /** Add symbols to constraint, correctly handling inter-dependencies.
   *
   * @see [[ConstraintHandling.addToConstraint]]
   */
  def addToConstraint(syms: List[Symbol])(using Context): Boolean
  def addToConstraint(sym: Symbol)(using Context): Boolean = addToConstraint(sym :: Nil)

  /** Further constrain a symbol already present in the constraint. */
  def addBound(sym: Symbol, bound: Type, isUpper: Boolean)(using Context): Boolean

  /** Is the symbol registered in the constraint?
   *
   * @note this is true even if the symbol is constrained to be equal to another type, unlike [[Constraint.contains]].
   */
  def contains(sym: Symbol)(using Context): Boolean

  def isEmpty: Boolean
  final def nonEmpty: Boolean = !isEmpty

  /** See [[ConstraintHandling.approximation]] */
  def approximation(sym: Symbol, fromBelow: Boolean)(using Context): Type

  def fresh: GadtConstraint

  /** Restore the state from other [[GadtConstraint]], probably copied using [[fresh]] */
  def restore(other: GadtConstraint): Unit

  def debugBoundsDescription(using Context): String

  def constraintPatternType(pat: Type, scrut: Type)(using Context): Boolean
}

final class ProperGadtConstraint private(
  private var knowledge: Knowledge,
  private var working: Boolean
) extends GadtConstraint {
  import dotty.tools.dotc.config.Printers.{gadts, gadtsConstr}

  def this() = this(
    knowledge = new Knowledge,
    working = false
  )

  inline private def performWork[T](inline op: => T): T =
    working = true
    val res = op
    working = false
    res

  /** Exposes ConstraintHandling.subsumes */
  def subsumes(left: GadtConstraint, right: GadtConstraint, pre: GadtConstraint)(using Context): Boolean = {
//    def extractConstraint(g: GadtConstraint) = g match {
//      case s: ProperGadtConstraint => s.constraint
//      case EmptyGadtConstraint => OrderingConstraint.empty
//    }
//    subsumes(extractConstraint(left), extractConstraint(right), extractConstraint(pre))

    // TODO: there is a restore in necessaryEither that we can't avoid because symbols keep getting added ?
    false
  }

  override def constraintPatternType(pat: Type, scrut: Type)(using Context): Boolean = performWork {
    val res = knowledge.constraintPatternType(pat, scrut)
//    println("Knowledge now:")
//    println(debugBoundsDescription)
    res
  }

  override def addToConstraint(params: List[Symbol])(using ctx: Context): Boolean = performWork {
    knowledge.addSymbols(params)
  }

  override def addBound(sym: Symbol, bound: Type, isUpper: Boolean)(using Context): Boolean = performWork {
    knowledge.addBound(sym, bound, isUpper)
  }

  override def isLess(sym1: Symbol, sym2: Symbol)(using Context): Boolean = performWork {
    knowledge.isLess(sym1, sym2)
  }

  override def fullBounds(sym: Symbol)(using ctx: Context): TypeBounds = performWork {
    // TODO: ???
    bounds(sym)
  }

  override def bounds(sym: Symbol)(using ctx: Context): TypeBounds = performWork {
    knowledge.findECForSym(sym)
      // TODO: Bounds may return ordering between syms, which the doc comment says that it does not...
      .map((ec, _) => knowledge.bounds(ec, inclusive = false))
      .getOrElse(null)
  }

  override def contains(sym: Symbol)(using Context): Boolean =
    knowledge.findECForSym(sym).isDefined

  override def approximation(sym: Symbol, fromBelow: Boolean)(using Context): Type = {
//    val res = approximation(tvarOrError(sym).origin, fromBelow = fromBelow)
//    gadts.println(i"approximating $sym ~> $res")
//    res
    ???
  }

  override def fresh: GadtConstraint =
    assert(!working)
    new ProperGadtConstraint(knowledge.fresh, working = false)

  def restore(other: GadtConstraint): Unit =
    assert(!working)
    other match {
      case other: ProperGadtConstraint =>
        this.knowledge = other.knowledge
      case _ =>
    }

  override def isEmpty: Boolean = knowledge.isEmpty

  // ---- Protected/internal -----------------------------------------------
  /*
  override protected def constraint = knowledge.asConstraint
  override protected def constraint_=(c: Constraint) = ??? // myConstraint = c

  override protected def isSub(tp1: Type, tp2: Type)(using Context): Boolean = TypeComparer.isSubType(tp1, tp2)
  override protected def isSame(tp1: Type, tp2: Type)(using Context): Boolean = TypeComparer.isSameType(tp1, tp2)

  override def nonParamBounds(param: TypeParamRef)(using Context): TypeBounds =
    ???
    /*
    val externalizeMap = new TypeMap {
      def apply(tp: Type): Type = tp match {
        case tpr: TypeParamRef => externalize(tpr)
        case tp => mapOver(tp)
      }
    }
    externalizeMap(constraint.nonParamBounds(param)).bounds
    */

  override def fullLowerBound(param: TypeParamRef)(using Context): Type =
    ???
    /*
    constraint.minLower(param).foldLeft(nonParamBounds(param).lo) {
      (t, u) => t | externalize(u)
    }
    */

  override def fullUpperBound(param: TypeParamRef)(using Context): Type =
    ???
    /*
    constraint.minUpper(param).foldLeft(nonParamBounds(param).hi) { (t, u) =>
      val eu = externalize(u)
      // Any as the upper bound means "no bound", but if F is higher-kinded,
      // Any & F = F[_]; this is wrong for us so we need to short-circuit
      if t.isAny then eu else t & eu
    }
    */

  // ---- Private ----------------------------------------------------------

  private def externalize(param: TypeParamRef)(using Context): Type =
    reverseMapping(param) match {
      case sym: Symbol => sym.typeRef
      case null => param
    }

  private def tvarOrError(sym: Symbol)(using Context): TypeVar =
    mapping(sym).ensuring(_ ne null, i"not a constrainable symbol: $sym")

  private def containsNoInternalTypes(
    tp: Type,
    acc: TypeAccumulator[Boolean] = null
  )(using Context): Boolean = tp match {
    case tpr: TypeParamRef => !reverseMapping.contains(tpr)
    case tv: TypeVar => !reverseMapping.contains(tv.origin)
    case tp =>
      (if (acc ne null) acc else new ContainsNoInternalTypesAccumulator()).foldOver(true, tp)
  }

  private class ContainsNoInternalTypesAccumulator(using Context) extends TypeAccumulator[Boolean] {
    override def apply(x: Boolean, tp: Type): Boolean = x && containsNoInternalTypes(tp)
  }
  */
  // ---- Debug ------------------------------------------------------------

//  override def constr = gadtsConstr

  override def toText(printer: Printer): Texts.Text = ???

  override def debugBoundsDescription(using Context): String = {
//    val sb = new mutable.StringBuilder
//    sb ++= constraint.show
//    sb += '\n'
//    mapping.foreachBinding { case (sym, _) =>
//      sb ++= i"$sym: ${fullBounds(sym)}\n"
//    }
//    sb.result
    knowledge.debugString
  }
}

@sharable object EmptyGadtConstraint extends GadtConstraint {
  override def bounds(sym: Symbol)(using Context): TypeBounds = null
  override def fullBounds(sym: Symbol)(using Context): TypeBounds = null

  override def isLess(sym1: Symbol, sym2: Symbol)(using Context): Boolean = unsupported("EmptyGadtConstraint.isLess")

  override def isEmpty: Boolean = true

  override def contains(sym: Symbol)(using Context) = false

  override def constraintPatternType(pat: Type, scrut: Type)(using Context): Boolean = unsupported("EmptyGadtConstraint.constraintPatternType")
  override def addToConstraint(params: List[Symbol])(using Context): Boolean = unsupported("EmptyGadtConstraint.addToConstraint")
  override def addBound(sym: Symbol, bound: Type, isUpper: Boolean)(using Context): Boolean = unsupported("EmptyGadtConstraint.addBound")

  override def approximation(sym: Symbol, fromBelow: Boolean)(using Context): Type = unsupported("EmptyGadtConstraint.approximation")

  override def fresh = new ProperGadtConstraint
  override def restore(other: GadtConstraint): Unit =
    if (!other.isEmpty) sys.error("cannot restore a non-empty GADTMap")

  override def debugBoundsDescription(using Context): String = "EmptyGadtConstraint"

  override def toText(printer: Printer): Texts.Text = "EmptyGadtConstraint"
}
