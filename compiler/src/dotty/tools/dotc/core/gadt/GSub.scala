package dotty.tools
package dotc
package core
package gadt

import scala.collection.mutable

class GSub:
  val edges: mutable.Map[Int, mutable.ArrayBuffer[Int]] = mutable.Map.empty
  val revEdges: mutable.Map[Int, mutable.ArrayBuffer[Int]] = mutable.Map.empty

  def addIneq(a: Int, b: Int) =
    assert(chain(b, a).isEmpty)
    val es1 = edges.getOrElseUpdate(a, mutable.ArrayBuffer.empty)
    es1 += b
    val es2 = edges.getOrElseUpdate(b, mutable.ArrayBuffer.empty)
    es2 += a

  def dfs(from: Int, theEdges: mutable.Map[Int, mutable.ArrayBuffer[Int]]): Set[Int] =
    val stack = mutable.Stack.fill(1)(from)
    val seen = mutable.Set.empty[Int]
    while stack.nonEmpty do
      val v = stack.pop()
      if !seen.contains(v) then
        seen += v
        theEdges.getOrElse(v, mutable.ArrayBuffer.empty)
          .foreach(stack.push)
    seen.toSet

  def chain(from: Int, to: Int): Option[Seq[Int]] =
    val stack = mutable.Stack.fill(1)((from, Seq(from)))
    val seen = mutable.Set.empty[Int]

    while stack.nonEmpty do
      val (v, paths) = stack.pop()
      assert(paths.last == v)
      if v == to then
        return Some(paths)
      if !paths.contains(v) then
        seen += v
        edges.getOrElse(v, mutable.ArrayBuffer.empty)
          .foreach(next => stack.push((next, paths :+ next)))
    None
