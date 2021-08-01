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
//    println(s"WE ADD $a <: $b  CURRENTLY")
//    println(debugString)
    assert(chain(b, a).isEmpty)
    val es1 = edges.getOrElseUpdate(a, mutable.Set.empty)
    es1 += b
    val es2 = revEdges.getOrElseUpdate(b, mutable.Set.empty)
    es2 += a
//    println(s"NOW HAVE")
//    println(debugString)

  def removeIneq(a: ECH, b: ECH): Unit =
    // assert(edges.contains(a) == edges.contains(b)) TODO: ???
    if edges.contains(a) then
      edges(a) -= b
    if revEdges.contains(b) then
      revEdges(b) -= a

  def remove(a: ECH): Unit =
    edges -= a
    edges.values.foreach(_ -= a)
    revEdges -= a
    revEdges.values.foreach(_ -= a)

  def containsEdge(a: ECH, b: ECH): Boolean =
    edges.get(a).map(_.contains(b)).getOrElse(false)

  def merge(a: ECH, b: ECH, ab: ECH): Unit =
    println(s"MERGE GSUB OF $a AND $b INTO $ab   WHERE")
    println(debugString)
    assert(chain(a, b).nonEmpty || chain(b, a).nonEmpty)
    // TODO: check this
    val allLower = strictLowerBounds(a) ++ strictLowerBounds(b) + a + b
    val allUpper = strictUpperBounds(a) ++ strictUpperBounds(b) + a + b
    val forward = allLower.flatMap(l => allUpper.map(u => (l, u)))
      .filterNot((l, u) =>
        // TODO: OK?
        (u == ab && containsEdge(l, a) && containsEdge(l, b)) ||
        (l == ab && containsEdge(a, u) && containsEdge(b, u))
      )
    val lower = revEdges.getOrElse(a, mutable.Set.empty).toSet.filter(_ != b)
      ++ revEdges.getOrElse(b, mutable.Set.empty).toSet.filter(_ != a)
    val upper = edges.getOrElse(a, mutable.Set.empty).toSet.filter(_ != b)
      ++ edges.getOrElse(b, mutable.Set.empty).toSet.filter(_ != a)
    val extra = lower.map(l => (l, ab)) ++ upper.map(u => (ab, u))

    remove(a)
    remove(b)
    forward.foreach((v1, v2) => removeIneq(v1, v2))
    println("LOWER: "+lower)
    println("UPPER: "+upper)
    println("FWD: "+forward)
    // TODO
    //    (extra -- forward).foreach((v1, v2) => addIneq(v1, v2))
    extra.foreach((v1, v2) => addIneq(v1, v2))
    println("WE NOW HAVE:")
    println(debugString)

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
    val stack = mutable.Stack((from, Seq(from)))
    val seen = mutable.Set.empty[ECH]
//    println(s"CHAIN $from TO $to  KNOWING THAT:")
//    println(debugString)
    while stack.nonEmpty do
      val (v, paths) = stack.pop()
      assert(paths.last == v)
      if v == to then
//        println(s"YES: $paths")
        return Some(paths)
      if !seen.contains(v) then
        seen += v
        edges.get(v).foreach(
          _.foreach(next => stack.push((next, paths :+ next))))
//    println("NOPE")
    None

  def debugString: String =
    if edges.isEmpty then
      "(empty gsub)"
    else
      edges.foldLeft(Seq.empty[String]) {
        case (acc, (ec, his)) =>
          acc :+ s"""[$ec] <: {${his.map(hi => s"[$hi]").mkString(", ")}}"""
      }.mkString("\n")