package dotty.tools
package dotc
package core
package gadt

import Types._
import Decorators._
import Symbols._
import Contexts._
import UnionFind.ECH

object ExtraTypes {

  final class DNF(val disjunctions: Set[Set[Type]], val theType: Type) extends TypeProxy with TermType {
    def underlying(using Context): Type = theType

    override def hash: Int = theType.hash

    override def computeHash(bs: Hashable.Binders): Int = theType.computeHash(bs)
  }

  object DNF {
    def apply(disjunctions: Set[Set[Type]])(using Context): DNF = {
      val theType: Type =
        disjunctions.map(conj => conj.reduce(AndType.make(_, _)))
          .reduce(OrType.make(_, _, false)) // TODO: What is a "soft union" ?
      new DNF(disjunctions, theType)
    }

    def unapply(dnf: DNF): Some[Set[Set[Type]]] = Some(dnf.disjunctions)
  }

  ///////////////////////////////////

  final case class ECType(ec: ECH) extends TypeProxy with TermType {
    def underlying(using ctx: Context): Type = ctx.property(Gadt.KnowledgeKey).get.typeReprOf(ec)

    override def hash: Int = ec.hash

    override def computeHash(bs: Hashable.Binders): Int = ec.hash
  }

  final case class AppliedECType(ec: ECH, args: List[Type]) extends TypeProxy with TermType {
    def underlying(using ctx: Context): Type =
      val k = ctx.property(Gadt.KnowledgeKey).get
      val repr = k.typeReprOf(ec)
      assert(repr.isInstanceOf[HKTypeLambda])
      repr.appliedTo(args)

    override def hash: Int = ec.hash

    override def computeHash(bs: Hashable.Binders): Int = ec.hash
  }

}
