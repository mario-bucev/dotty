package dotty.tools
package dotc
package core
package gadt

import collection.mutable

object UnionFind:
  opaque type ECH = Int

  extension (ech: ECH)
    def hash: Int = java.util.Objects.hash(ech)
    def toInt: Int = ech

  // TODO: No better way to do so ??

  class UnionFind:
    val elems: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty
    val sizes: mutable.ArrayBuffer[Int] = mutable.ArrayBuffer.empty

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
