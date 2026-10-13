package cuvee.prove

import util.Rational
import cuvee.core._

// an immutable collection of facts of some theory, which records the facts it can express and ignores the others,
// and which detects when they contradict each other (after cuvee.simplify.Theory)
trait Theory:
  def inconsistent: Boolean
  def assume(expr: Expr): Theory
  def deny(expr: Expr): Theory

object Facts:
  val empty = Facts(Nil, Nil, false)

// the facts as given, the assumptions are known to hold, the conclusions are known not to hold;
// they are inconsistent if false is among the assumptions, true among the conclusions, or a fact among both
// (copied from cuvee.simplify.Facts)
case class Facts(assms: List[Expr], concls: List[Expr], inconsistent: Boolean) extends Theory:
  def assume(expr: Expr): Facts =
    val conflict = expr == False || (concls contains expr)
    Facts(expr :: assms, concls, inconsistent || conflict)

  def deny(expr: Expr): Facts =
    val conflict = expr == True || (assms contains expr)
    Facts(assms, expr :: concls, inconsistent || conflict)

  // a fact that is not recorded, e.g. an equation of variables kept in the classes, still conflicts with the conclusions
  def check(expr: Expr): Facts =
    val conflict = expr == False || (concls contains expr)
    Facts(assms, concls, inconsistent || conflict)

  def free: Set[Var] =
    assms.free ++ concls.free

object Linear:
  val empty = Linear(Nil, Nil, Map())

// the linear constraints on Int and Real among the facts, decided by the simplex over the rationals (see Simplex),
// which replaces the difference constraints of the simplifier: comparisons and equations as constraints 0 <= p and
// 0 < p, where on Int a strict comparison is the non-strict one offset by 1 and the coefficients are rounded
// (Poly.floor), such that e.g. 2 * n < 52 bounds n by 25; disequations on Int and Real are kept apart and contradict
// the constraints if these determine the value of the difference; the solutions of linear equations for a variable,
// e.g. x by 40 - n for n + x == 40, are recorded as `solved` and inlined into polynomials by the simplifier (see
// Simplify.poly), while the equation remains a constraint
case class Linear(constraints: List[Constraint], diseqs: List[(Ring, Poly)], solved: Map[Var, Expr]) extends Theory:
  // a disequation p != 0 is refuted if the constraints bound p to 0 from both sides
  lazy val inconsistent: Boolean =
    !Simplex.satisfiable(constraints) || diseqs.exists: (ring, poly) =>
      !Simplex.satisfiable(positive(ring, poly) :: constraints) && !Simplex.satisfiable(positive(ring, -poly) :: constraints)

  // 0 < p, on Int as 0 <= p - 1
  def positive(ring: Ring, poly: Poly): Constraint =
    if ring == Ints.ring
    then Constraint((poly - Poly.one).normalize.floor, strict = false)
    else Constraint(poly.normalize, strict = true)

  def assume(expr: Expr): Linear =
    expr match
      case Not(phi)                              => deny(phi)
      case Ints.le(left, right)                  => le(Ints.ring, left, right)
      case Ints.lt(left, right)                  => lt(Ints.ring, left, right)
      case Ints.ge(left, right)                  => le(Ints.ring, right, left)
      case Ints.gt(left, right)                  => lt(Ints.ring, right, left)
      case Reals.le(left, right)                 => le(Reals.ring, left, right)
      case Reals.lt(left, right)                 => lt(Reals.ring, left, right)
      case Reals.ge(left, right)                 => le(Reals.ring, right, left)
      case Reals.gt(left, right)                 => lt(Reals.ring, right, left)
      case Eq(left, right) if Ring(left.typ).isDefined =>
        val Some(ring) = Ring(left.typ): @unchecked
        le(ring, left, right).le(ring, right, left).solve(ring, left, right)
      case _                                     => this

  def deny(expr: Expr): Linear =
    expr match
      case Not(phi)                              => assume(phi)
      case Ints.le(left, right)                  => lt(Ints.ring, right, left)
      case Ints.lt(left, right)                  => le(Ints.ring, right, left)
      case Ints.ge(left, right)                  => lt(Ints.ring, left, right)
      case Ints.gt(left, right)                  => le(Ints.ring, left, right)
      case Reals.le(left, right)                 => lt(Reals.ring, right, left)
      case Reals.lt(left, right)                 => le(Reals.ring, right, left)
      case Reals.ge(left, right)                 => lt(Reals.ring, left, right)
      case Reals.gt(left, right)                 => le(Reals.ring, left, right)
      case Eq(left, right) if Ring(left.typ).isDefined =>
        val Some(ring) = Ring(left.typ): @unchecked
        copy(diseqs = (ring, (Arith.toPoly(ring, left) - Arith.toPoly(ring, right)).normalize) :: diseqs)
      case _                                     => this

  def le(ring: Ring, left: Expr, right: Expr): Linear =
    add(ring, Constraint.le(Arith.toPoly(ring, left), Arith.toPoly(ring, right)))

  def lt(ring: Ring, left: Expr, right: Expr): Linear =
    if ring == Ints.ring
    then add(ring, Constraint.le(Arith.toPoly(ring, left) + Poly.one, Arith.toPoly(ring, right)))
    else add(ring, Constraint.lt(Arith.toPoly(ring, left), Arith.toPoly(ring, right)))

  // on Int, the coefficients are rounded, which is exact for integers (Poly.floor)
  def add(ring: Ring, c: Constraint): Linear =
    val c_ = if ring == Ints.ring then Constraint(c.poly.floor, c.strict) else c
    if constraints.contains(c_) then this else copy(constraints = c_ :: constraints)

  // the first solution of a linear equation for a variable that is not solved yet, if it is an arithmetic
  // expression (see Poly.solution); equations with a variable or a literal are classes (see Classes)
  def solve(ring: Ring, left: Expr, right: Expr): Linear =
    val poly = (Arith.toPoly(ring, left) - Arith.toPoly(ring, right)).normalize
    val solution =
      for
        (x, rest) <- poly.solution((x, _) => !(solved contains x))
        e = rest.toExpr(ring)
        if e.isArith
      yield (x, e)
    solution match
      case Some(pair) => copy(solved = solved + pair)
      case None       => this
