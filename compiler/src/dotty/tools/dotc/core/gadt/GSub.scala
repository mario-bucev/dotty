package dotty.tools
package dotc
package core
package gadt

import UnionFind.ECH
import scala.collection.mutable

class GSub:
  val edges: mutable.Map[ECH, mutable.Set[ECH]] = mutable.Map.empty
  val revEdges: mutable.Map[ECH, mutable.Set[ECH]] = mutable.Map.empty

  def strictLowerBounds(a: ECH): Set[ECH] =
    dfs(a, revEdges) - a

  def strictUpperBounds(a: ECH): Set[ECH] =
    dfs(a, edges) - a

  def addIneq(a: ECH, b: ECH): Unit =
    assert(chain(b, a).isEmpty)
    val es1 = edges.getOrElseUpdate(a, mutable.Set.empty)
    es1 += b
    val es2 = edges.getOrElseUpdate(b, mutable.Set.empty)
    es2 += a

  def removeIneq(a: ECH, b: ECH): Unit =
    assert(edges.contains(a) == edges.contains(b))
    if edges.contains(a) then
      edges(a) -= b
      revEdges(b) -= a

  def remove(a: ECH): Unit =
    edges -= a
    edges.values.foreach(_ -= a)
    revEdges -= a
    revEdges.values.foreach(_ -= a)

  def containsEdge(a: ECH, b: ECH): Boolean =
    edges.get(a).map(_.contains(b)).getOrElse(false)

  def merge(a: ECH, b: ECH, ab: ECH): Unit =
    assert(chain(a, b).nonEmpty || chain(b, a).nonEmpty)
    val allLower = strictLowerBounds(a) ++ strictLowerBounds(b) + a + b
    val allUpper = strictUpperBounds(a) ++ strictUpperBounds(b) + a + b
    val forward = allLower.flatMap(l => allUpper.map(u => (l, u)))
      .filterNot((l, u) =>
        // TODO: OK?
        u == ab && containsEdge(l, a) && containsEdge(l, b) ||
        l == ab && containsEdge(a, u) && containsEdge(b, u)
      )
    val lower = revEdges(a).toSet.filter(_ != b) ++ revEdges(b).toSet.filter(_ != a)
    val upper = edges(a).toSet.filter(_ != b) ++ edges(a).toSet.filter(_ != b)
    val extra = lower.map(l => (l, ab)) ++ upper.map(u => (ab, u))

    remove(a)
    remove(b)
    forward.foreach((v1, v2) => removeIneq(v1, v2))
    (extra -- forward).foreach((v1, v2) => addIneq(v1, v2))

  private def dfs(from: ECH, theEdges: mutable.Map[ECH, mutable.Set[ECH]]): Set[ECH] =
    val stack = mutable.Stack.fill(1)(from)
    val seen = mutable.Set.empty[ECH]
    while stack.nonEmpty do
      val v = stack.pop()
      if !seen.contains(v) then
        seen += v
        theEdges.getOrElse(v, mutable.ArrayBuffer.empty)
          .foreach(stack.push)
    seen.toSet

  def chain(from: ECH, to: ECH): Option[Seq[ECH]] =
    val stack = mutable.Stack.fill(1)((from, Seq(from)))
    val seen = mutable.Set.empty[ECH]

    while stack.nonEmpty do
      val (v, paths) = stack.pop()
      assert(paths.last == v)
      if v == to then
        return Some(paths)
      if !paths.contains(v) then
        seen += v
        edges.get(v).foreach(
          _.foreach(next => stack.push((next, paths :+ next))))
    None
