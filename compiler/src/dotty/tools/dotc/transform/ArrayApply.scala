package dotty.tools.dotc
package transform

import core._
import MegaPhase._
import Contexts.Context
import Symbols._
import Types._
import StdNames._
import ast.Trees._
import dotty.tools.dotc.ast.tpd

import scala.reflect.ClassTag


/** This phase rewrites calls to `Array.apply` to primitive array instantion.
 *
 *  Transforms `scala.Array.apply([....])` and `scala.Array.apply(..., [....])` into `[...]`
 */
class ArrayApply extends MiniPhase {
  import tpd._

  override def phaseName: String = "arrayApply"

  override def transformApply(tree: tpd.Apply)(implicit ctx: Context): tpd.Tree = {
    if (tree.symbol.name == nme.apply && tree.symbol.owner == defn.ArrayModule) { // Is `Array.apply`
      tree.args match {
        case CleanTree(Apply(wrapRefArrayMeth, (seqLit: tpd.JavaSeqLiteral) :: Nil)) :: ct :: Nil
            if defn.WrapArrayMethods().contains(wrapRefArrayMeth.symbol) && elideClassTag(ct) =>
          seqLit

        case elem0 :: CleanTree(Apply(wrapRefArrayMeth, (seqLit: tpd.JavaSeqLiteral) :: Nil)) :: Nil
            if defn.WrapArrayMethods().contains(wrapRefArrayMeth.symbol) =>
          tpd.JavaSeqLiteral(elem0 :: seqLit.elems, seqLit.elemtpt)

        case _ =>
          tree
      }

    } else tree
  }

  /** Only optimize when classtag if it is one of
   *  - `ClassTag.apply(classOf[X])`
   *  - `ClassTag.apply(java.lang.XYZ.Type)`
   *  - `ClassTag.{Byte, Boolean, ...}`
   */
  private def elideClassTag(ct: Tree)(implicit ctx: Context): Boolean = ct match {
    case Apply(_, rc :: Nil) if ct.symbol == defn.ClassTagModule_apply =>
      rc match {
        case _: Literal => true // classOf[X]
        case rc: RefTree if rc.name == nme.TYPE_ =>
          val owner = rc.symbol.maybeOwner.companionModule
          owner == defn.BoxedBooleanModule || owner == defn.BoxedByteModule ||
          owner == defn.BoxedShortModule || owner == defn.BoxedCharModule ||
          owner == defn.BoxedIntModule || owner == defn.BoxedLongModule ||
          owner == defn.BoxedFloatModule || owner == defn.BoxedDoubleModule ||
          owner == defn.BoxedUnitModule
        case _ => false
      }
    case Apply(ctm: RefTree, _) if ctm.symbol.maybeOwner.companionModule == defn.ClassTagModule =>
      nme.ScalaValueNames.contains(ctm.name)
    case _ => false
  }

  object CleanTree {
    def unapply(tree: Tree)(implicit ctx: Context): Some[Tree] = tree match {
      case Block(Nil, expr) => unapply(expr)
      case Typed(expr, _) => unapply(expr)
      case _ => Some(tree)
    }
  }
}
