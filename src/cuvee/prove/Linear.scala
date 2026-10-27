package cuvee.prove

import util.Rational
import cuvee.core._

object Linear:
  def empty = Linear(Nil, Nil, Tableau.empty)

// the linear constraints on Int and Real among the facts, decided by the simplex over the rationals (see Simplex):
// comparisons and equations as constraints 0 <= p and 0 < p, where on Int a strict comparison is the non-strict one
// offset by 1 and the coefficients are rounded (Poly.floor), such that e.g. 2 * n < 52 bounds n by 25; disequations
// are kept apart and contradict the constraints if these determine the value of the difference; the solutions of
// linear equations are kept by the classes (see Classes.solve)
// the constraints are kept in the tableau of the simplex as well, solved incrementally (see Tableau)
case class Linear(constraints: List[Constraint], diseqs: List[(Ring, Poly)], tableau: Tableau) extends Theory:
  // a disequation p != 0 is refuted if the constraints bound p to 0 from both sides
  lazy val inconsistent: Boolean =
    !tableau.sat || diseqs.exists: (ring, poly) =>
      !tableau.add(positive(ring, poly)).sat && !tableau.add(positive(ring, -poly)).sat

  // the integer variables among `xs` that the constraints fix to a value, e.g. k of 0 <= k and k < n with n <= 1: the
  // value of k in the solved tableau is the only candidate, confirmed if a smaller and a larger value contradict the
  // constraints, which the incremental tableau decides with two constraints added to it
  def fixed(xs: List[Var]): List[(Var, BigInt)] =
    for
      x <- xs if tableau.sat && x.typ == Sort.int
      i <- tableau.atoms.get(List((x, BigInt(1)))).toList
      v = tableau.value(i) if v.d.isZero && v.c.den == 1
      n = v.c.num
      if !tableau.add(Constraint.le(Poly.atom(x), Poly.const(Rational(n - 1)))).sat
      if !tableau.add(Constraint.le(Poly.const(Rational(n + 1)), Poly.atom(x))).sat
    yield (x, n)

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
        le(ring, left, right).le(ring, right, left)
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

  // on Int, the coefficients are rounded, which is exact for integers (Poly.floor); an atom t div k or t mod k for a
  // literal k != 0 brings the definition of both by SMT-LIB, t == k * (t div k) + t mod k with 0 <= t mod k <= |k| - 1,
  // which bounds the quotient as well (k * (t div k) <= t <= k * (t div k) + k - 1 for k > 0, the binary search's
  // midpoint l <= (h + l) / 2 < h for l < h) and relates the two, e.g. t == 2 * n for t % 2 == 0 and t / 2 == n
  // (array-tiling/pr2); added once with the first constraint that mentions either atom, so a denied atom gets it as
  // well; t is smaller than the atoms, so its own divisions terminate, and the definition mentions only the two atoms
  // of t and k, whose definitions are then known
  def add(ring: Ring, c: Constraint): Linear =
    val c_ = if ring == Ints.ring then Constraint(c.poly.floor, c.strict) else c
    if constraints.contains(c_)
    then this
    else
      val divisions =
        for
          mono <- c_.poly.monos
          (atom, _) <- mono.atoms
          (t, k, n) <- atom match
            case Ints.div(t, k @ Ints.ring.num(n: BigInt)) if ring == Ints.ring && n != 0 => List((t, k, n))
            case Ints.mod(t, k @ Ints.ring.num(n: BigInt)) if ring == Ints.ring && n != 0 => List((t, k, n))
            case _                                                                      => Nil
        yield (t, k, n)
      divisions.distinct.foldLeft(copy(constraints = c_ :: constraints, tableau = tableau.add(c_))) { case (linear, (t, k, n)) =>
        val q = Poly.atom(Ints.div(t, k))
        val r = Poly.atom(Ints.mod(t, k))
        val t_ = Arith.toPoly(ring, t)
        val definition = q * Rational(n) + r
        linear
          .add(ring, Constraint.le(definition, t_))
          .add(ring, Constraint.le(t_, definition))
          .add(ring, Constraint.le(Poly.zero, r))
          .add(ring, Constraint.le(r, Poly.const(Rational(n.abs - 1))))
      }
