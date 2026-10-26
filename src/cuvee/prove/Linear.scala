package cuvee.prove

import util.Rational
import cuvee.core._

object Linear:
  def empty = Linear(Nil, Nil, util.Ref(Map()))

  // the results of the checks by the set of constraints and disequations, shared by the copies of a context and fresh
  // for each command (see Context.withRules), since the same check is made at many positions
  type Checks = Map[(Set[Constraint], Set[(Ring, Poly)]), Boolean]

// the linear constraints on Int and Real among the facts, decided by the simplex over the rationals (see Simplex):
// comparisons and equations as constraints 0 <= p and 0 < p, where on Int a strict comparison is the non-strict one
// offset by 1 and the coefficients are rounded (Poly.floor), such that e.g. 2 * n < 52 bounds n by 25; disequations
// are kept apart and contradict the constraints if these determine the value of the difference; the solutions of
// linear equations are kept by the classes (see Classes.solve)
case class Linear(constraints: List[Constraint], diseqs: List[(Ring, Poly)], checks: util.Ref[Linear.Checks]) extends Theory:
  // a disequation p != 0 is refuted if the constraints bound p to 0 from both sides; the check is cached (see checks)
  lazy val inconsistent: Boolean =
    val key = (constraints.toSet, diseqs.toSet)
    checks.value.get(key) match
      case Some(result) =>
        result

      case None =>
        val result = !Simplex.satisfiable(constraints) || diseqs.exists: (ring, poly) =>
          !Simplex.satisfiable(positive(ring, poly) :: constraints) && !Simplex.satisfiable(positive(ring, -poly) :: constraints)
        checks := checks.value + (key -> result)
        result

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

  // on Int, the coefficients are rounded, which is exact for integers (Poly.floor); an atom t div k for a positive
  // literal k brings its bounds k * (t div k) <= t <= k * (t div k) + k - 1 (with t div k rounding down, as in the
  // binary search's midpoint, l <= (h + l) / 2 < h for l < h), and an atom t mod k for a literal k != 0 its range
  // 0 <= t mod k <= |k| - 1, added once with the first constraint that mentions it, so a denied atom gets them as
  // well; t is smaller than the atom, so its own divisions terminate, and a range mentions only its atom
  def add(ring: Ring, c: Constraint): Linear =
    val c_ = if ring == Ints.ring then Constraint(c.poly.floor, c.strict) else c
    if constraints.contains(c_)
    then this
    else
      val divisions =
        for
          mono <- c_.poly.monos
          case (atom @ Ints.div(t, Ints.ring.num(k: BigInt)), _) <- mono.atoms
          if ring == Ints.ring && k > 0
        yield (Arith.toPoly(ring, t), Poly.atom(atom) * Rational(k), Rational(k - 1))
      val remainders =
        for
          mono <- c_.poly.monos
          case (atom @ Ints.mod(_, Ints.ring.num(k: BigInt)), _) <- mono.atoms
          if ring == Ints.ring && k != 0
        yield (Poly.atom(atom), Rational(k.abs - 1))
      val linear = divisions.distinct.foldLeft(copy(constraints = c_ :: constraints)) { case (linear, (t, d, offset)) =>
        linear.add(ring, Constraint.le(d, t)).add(ring, Constraint.le(t, d + Poly.const(offset)))
      }
      remainders.distinct.foldLeft(linear) { case (linear, (r, max)) =>
        linear.add(ring, Constraint.le(Poly.zero, r)).add(ring, Constraint.le(r, Poly.const(max)))
      }
