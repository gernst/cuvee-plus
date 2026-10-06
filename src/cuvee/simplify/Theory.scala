package cuvee.simplify

import cuvee.core._

// an immutable collection of facts of some theory, which records the facts it can express and ignores the others,
// and which detects when they contradict each other
trait Theory:
  def inconsistent: Boolean
  def assume(expr: Expr): Theory
  def deny(expr: Expr): Theory

object Facts:
  val empty = Facts(Nil, Nil)

// the facts as given, the assumptions are known to hold, the conclusions are known not to hold;
// they are inconsistent if false is among the assumptions or true among the conclusions
case class Facts(assms: List[Expr], concls: List[Expr]) extends Theory:
  def inconsistent =
    (assms contains False) || (concls contains True)

  def assume(expr: Expr): Facts =
    copy(assms = expr :: assms)

  def deny(expr: Expr): Facts =
    copy(concls = expr :: concls)

  // the variables that occur in the facts
  def free: Set[Var] =
    assms.free ++ concls.free

object Differences:
  val empty = Differences(Set(), Map())

// difference constraints x - y <= c on Int, closed under the shortest paths (incremental Floyd-Warshall),
// adapted from Christopher David Lösbrock, Implementing an Incremental Solver for Difference Logic (BA thesis, RWTH);
// distance((x, y)) = c is the tightest known bound x - y <= c, bounds of a single atom x are relative to the node 0;
// atoms are arbitrary non-arithmetic terms, and monomials with a factor, e.g. 2 * x, are atoms as a whole,
// about which nothing else is known; facts that are no difference constraints are ignored
case class Differences(nodes: Set[Expr], distance: Map[(Expr, Expr), BigInt]) extends Theory:
  // a negative cycle, which the closure makes a negative distance of some node to itself
  def inconsistent =
    nodes exists (x => distance.get((x, x)) exists (_ < 0))

  def assume(expr: Expr): Differences =
    expr match
      case Not(phi)                              => deny(phi)
      case Le.int(left, right)                   => le(left, right)
      case Lt.int(left, right)                   => lt(left, right)
      case Ge.int(left, right)                   => le(right, left)
      case Gt.int(left, right)                   => lt(right, left)
      case Eq(left, right) if left.typ == Sort.int => le(left, right).le(right, left)
      case _                                     => this

  // on Int, the negation of a comparison is a comparison, whereas a disequation is not a difference constraint
  def deny(expr: Expr): Differences =
    expr match
      case Not(phi)            => assume(phi)
      case Le.int(left, right) => lt(right, left)
      case Lt.int(left, right) => le(right, left)
      case Ge.int(left, right) => lt(left, right)
      case Gt.int(left, right) => le(left, right)
      case _                   => this

  // left <= right as left - right <= 0
  def le(left: Expr, right: Expr): Differences =
    add(Arith.toPoly(Ring.int, left) - Arith.toPoly(Ring.int, right))

  // left < right as left - right + 1 <= 0, on Int
  def lt(left: Expr, right: Expr): Differences =
    add(Arith.toPoly(Ring.int, left) - Arith.toPoly(Ring.int, right) + Poly.one)

  // poly <= 0, which is a difference constraint if it has at most one atom of either sign;
  // with poly = (c1 + x) - (c2 + y), the constraint is x - y <= c2 - c1, where a missing atom is the node 0,
  // and a constant constraint that fails is a negative cycle of 0
  def add(poly: Poly): Differences =
    val (neg, pos) = poly.normalize.sides
    val c = (neg.const - pos.const).num

    (pos.monos, neg.monos) match
      case (List(x), List(y)) => add(x.toExpr(Ring.int), y.toExpr(Ring.int), c)
      case (List(x), Nil)     => add(x.toExpr(Ring.int), Zero.int, c)
      case (Nil, List(y))     => add(Zero.int, y.toExpr(Ring.int), c)
      case (Nil, Nil)         => if c < 0 then add(Zero.int, Zero.int, c) else this
      case _                  => this

  // from - to <= c, where every path x .. from .. to .. y may become shorter, which is O(n²) in the nodes
  def add(from: Expr, to: Expr, c: BigInt): Differences =
    var distance = this.distance

    def link(x: Expr, y: Expr, a: BigInt) =
      distance.get((x, y)) match
        // a negative self-cycle stays, since the facts are already inconsistent
        case Some(b) if x == y && b < 0 =>
        case Some(b) if b <= a          =>
        case _                          => distance += ((x, y) -> a)

    val nodes = this.nodes + from + to
    link(from, from, 0)
    link(to, to, 0)
    link(from, to, c)

    for
      x <- nodes
      y <- nodes
      if (distance contains (x, from)) && (distance contains (to, y))
    do link(x, y, distance((x, from)) + c + distance((to, y)))

    Differences(nodes, distance)
