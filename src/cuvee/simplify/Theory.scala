package cuvee.simplify

import cuvee.core._

// an immutable collection of facts of some theory, which records the facts it can express and ignores the others,
// and which detects when they contradict each other
trait Theory:
  def inconsistent: Boolean
  def assume(expr: Expr): Theory
  def deny(expr: Expr): Theory

object Facts:
  val empty = Facts(Nil, Nil, false)

// the facts as given, the assumptions are known to hold, the conclusions are known not to hold;
// they are inconsistent if false is among the assumptions, true among the conclusions, or a fact among both,
// which is recorded as the facts are added, such that a query (see Ctx.implied) needs a single pass over them
case class Facts(assms: List[Expr], concls: List[Expr], inconsistent: Boolean) extends Theory:
  def assume(expr: Expr): Facts =
    val conflict = expr == False || (concls contains expr)
    Facts(expr :: assms, concls, inconsistent || conflict)

  def deny(expr: Expr): Facts =
    val conflict = expr == True || (assms contains expr)
    Facts(assms, expr :: concls, inconsistent || conflict)

  // a fact that is not recorded, e.g. an equation in the substitution (see Ctx.assume), still conflicts with the conclusions
  def check(expr: Expr): Facts =
    val conflict = expr == False || (concls contains expr)
    Facts(assms, concls, inconsistent || conflict)

  // the variables that occur in the facts
  def free: Set[Var] =
    assms.free ++ concls.free

object Chains:
  val empty = Chains(Map(), Map())

// equations of variables, which are never inconsistent, since conflicting equations are not recorded:
// replace: a substitution that replaces variables by others or by literals known to be equal,
// or by the solution of an arithmetic equation, e.g. x by 40 - n for n + x == 40,
// whose equations are no facts of the context (see Ctx.assume);
// chain: the equations x == e that are not recursive, i.e., where x is not free in e,
// which remain facts of the context, such that they are still found by Simplify.implied;
// equations whose right-hand side is a sum, difference, negation, or product are not recorded,
// since rewriting follows the equations (see Rewrite.matches), whereas arithmetic is normalized instead
case class Chains(replace: Map[Var, Expr], chain: Map[Var, Expr]) extends Theory:
  def inconsistent =
    false

  def assume(expr: Expr): Chains =
    expr match
      case Eq(x: Var, y: Var) if replaces(x, y) =>
        copy(replace = replace + (x -> y))

      case Eq(x: Var, l: Lit) if replaces(x, l) =>
        copy(replace = replace + (x -> l))

      case Eq(l: Lit, x: Var) if replaces(x, l) =>
        copy(replace = replace + (x -> l))

      case Eq(left, right) if solve(left, right).nonEmpty =>
        copy(replace = replace + solve(left, right).get)

      case Eq(x: Var, e) if chains(x, e) =>
        copy(chain = chain + (x -> e))

      case Eq(e, x: Var) if chains(x, e) =>
        copy(chain = chain + (x -> e))

      case _ =>
        this

  def deny(expr: Expr): Chains =
    this

  // whether x == e can be recorded in the substitution, e is a variable or a literal
  def replaces(x: Var, e: Expr): Boolean =
    x != e && !(replace contains x)

  // the first solution of an arithmetic equation for a variable that is an arithmetic expression (see Poly.solutions),
  // single variables and literals are replaced above, other terms are chained below;
  // the substitution stays acyclic and is applied in one step (see Simplify.var_), since the solution contains no
  // variable that is replaced, and the variable occurs in no replacement, nor in a definition the solution depends on,
  // e.g. n by an expression over a trace K with K == counter(0, 1, n), which would loop (see Simplify.iterations)
  def solve(left: Expr, right: Expr): Option[(Var, Expr)] =
    Ring(left.typ) match
      case Some(ring) =>
        val poly = (Arith.toPoly(ring, left) - Arith.toPoly(ring, right)).normalize
        val solutions =
          for
            (x, rest) <- poly.solutions
            e = rest.toExpr(ring)
            if Ctx.arithmetic(e) && replaces(x, e)
            if (e.free intersect replace.keySet).isEmpty && !(replace.values.free contains x) && acyclic(x, e)
          yield (x, e)
        solutions.headOption

      case None =>
        None

  // whether x == e can be recorded in the chain
  def chains(x: Var, e: Expr): Boolean =
    !(chain contains x) && !(e.free contains x) && !Ctx.arithmetic(e) && acyclic(x, e)

  // whether e does not depend on x through the substitution and the chain, transitively
  def acyclic(x: Var, e: Expr): Boolean =
    def reach(todo: List[Var], seen: Set[Var]): Set[Var] =
      todo match
        case Nil => seen
        case y :: rest if seen contains y => reach(rest, seen)
        case y :: rest =>
          val next = (replace.get(y) ++ chain.get(y)).flatMap(_.free).toList
          reach(next ++ rest, seen + y)

    !reach(e.free.toList, Set()).contains(x)

  // the variables of the substitution, whose equations are not among the facts
  def free: Set[Var] =
    replace.keySet ++ replace.values.free

object Diffs:
  val empty = Diffs(Set(), Map())

// difference constraints x - y <= c on Int, closed under the shortest paths (incremental Floyd-Warshall),
// adapted from Christopher David Lösbrock, Implementing an Incremental Solver for Difference Logic (BA thesis, RWTH);
// distance((x, y)) = c is the tightest known bound x - y <= c, bounds of a single atom x are relative to the node 0;
// atoms are arbitrary non-arithmetic terms, and monomials with a factor, e.g. 2 * x, are atoms as a whole,
// about which nothing else is known; facts that are no difference constraints are ignored
case class Diffs(nodes: Set[Expr], distance: Map[(Expr, Expr), BigInt]) extends Theory:
  // a negative cycle, which the closure makes a negative distance of some node to itself
  def inconsistent =
    nodes exists (x => distance.get((x, x)) exists (_ < 0))

  def assume(expr: Expr): Diffs =
    expr match
      case Not(phi)                              => deny(phi)
      case Le.int(left, right)                   => le(left, right)
      case Lt.int(left, right)                   => lt(left, right)
      case Ge.int(left, right)                   => le(right, left)
      case Gt.int(left, right)                   => lt(right, left)
      case Eq(left, right) if left.typ == Sort.int => le(left, right).le(right, left)
      case _                                     => this

  // on Int, the negation of a comparison is a comparison, whereas a disequation is not a difference constraint
  def deny(expr: Expr): Diffs =
    expr match
      case Not(phi)            => assume(phi)
      case Le.int(left, right) => lt(right, left)
      case Lt.int(left, right) => le(right, left)
      case Ge.int(left, right) => lt(left, right)
      case Gt.int(left, right) => le(left, right)
      case _                   => this

  // left <= right as left - right <= 0
  def le(left: Expr, right: Expr): Diffs =
    add(Arith.toPoly(Ring.int, left) - Arith.toPoly(Ring.int, right))

  // left < right as left - right + 1 <= 0, on Int
  def lt(left: Expr, right: Expr): Diffs =
    add(Arith.toPoly(Ring.int, left) - Arith.toPoly(Ring.int, right) + Poly.one)

  // poly <= 0, which is a difference constraint if it has at most one atom of either sign;
  // with poly = (c1 + x) - (c2 + y), the constraint is x - y <= c2 - c1, where a missing atom is the node 0,
  // and a constant constraint that fails is a negative cycle of 0
  def add(poly: Poly): Diffs =
    val (neg, pos) = poly.normalize.sides
    val c = (neg.const - pos.const).num

    (pos.monos, neg.monos) match
      case (List(x), List(y)) => add(x.toExpr(Ring.int), y.toExpr(Ring.int), c)
      case (List(x), Nil)     => add(x.toExpr(Ring.int), Zero.int, c)
      case (Nil, List(y))     => add(Zero.int, y.toExpr(Ring.int), c)
      case (Nil, Nil)         => if c < 0 then add(Zero.int, Zero.int, c) else this
      case _                  => this

  // from - to <= c, where every path x .. from .. to .. y may become shorter, which is O(n²) in the nodes
  def add(from: Expr, to: Expr, c: BigInt): Diffs =
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

    Diffs(nodes, distance)
