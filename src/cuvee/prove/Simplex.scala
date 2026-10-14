package cuvee.prove

import util.Rational
import cuvee.core._

// a linear constraint 0 <= poly, or 0 < poly if strict, over the atoms of a normalized polynomial, whose monomials are
// linear in the atoms (monomials of higher degree are atoms of their own, see Linear.atom)
case class Constraint(poly: Poly, strict: Boolean):
  def atoms: Set[Expr] =
    poly.monos.flatMap(_.atoms.map(_._1)).toSet

  // the truth value of a constraint without atoms
  def holds: Option[Boolean] =
    if poly.monos.nonEmpty
    then None
    else if strict
    then Some(poly.const.isPositive)
    else Some(!poly.const.isNegative)

object Constraint:
  // left <= right and left < right
  def le(left: Poly, right: Poly) =
    Constraint((right - left).normalize, strict = false)

  def lt(left: Poly, right: Poly) =
    Constraint((right - left).normalize, strict = true)

// a rational c + d·δ with an infinitesimal δ > 0, by which strict bounds are expressed as non-strict ones (Dutertre
// and de Moura, A Fast Linear-Arithmetic Solver for DPLL(T), 2006)
case class Delta(c: Rational, d: Rational):
  def +(that: Delta) = Delta(c + that.c, d + that.d)
  def -(that: Delta) = Delta(c - that.c, d - that.d)
  def *(r: Rational) = Delta(c * r, d * r)
  def unary_- = Delta(-c, -d)

  def <(that: Delta): Boolean =
    c < that.c || (c == that.c && d < that.d)

  def <=(that: Delta): Boolean =
    this < that || this == that

object Delta:
  val zero = Delta(Rational(0), Rational(0))

// the general simplex over the rationals for the satisfiability of a conjunction of linear constraints, which is
// complete over the rationals: each distinct linear part Σ aᵢ xᵢ of the constraints is a slack variable with the
// bounds that the constraints give it, the atoms are the non-basic variables initially, and check pivots by Bland's
// rule until all basic variables are within their bounds (satisfiable) or some basic variable can not be fixed
// (unsatisfiable); strict bounds use Delta; the tableau is built per call, which suffices for the dozens of
// constraints of a context, incremental pivoting is a later optimization (see doc/prove.md)
object Simplex:
  // the linear part of a constraint with its leading coefficient positive, and the sign flipped if it was negated
  def linear(poly: Poly): (Poly, Boolean) =
    val lin = Poly(Rational(0), poly.monos)
    if lin.monos.headOption.exists(_.factor.isNegative) then (-lin, true) else (lin, false)

  def satisfiable(constraints: List[Constraint]): Boolean =
    constraints.flatMap(_.holds) match
      case flags if flags.contains(false) => false
      case _ => satisfiable_(constraints.filter(_.holds.isEmpty))

  def satisfiable_(constraints: List[Constraint]): Boolean =
    // the slack variables, one per distinct linear part, with their bounds: 0 <= c + lin is lin >= -c (lower bound),
    // and lin <= c if the linear part was negated (upper bound); strict bounds are offset by δ
    val rows = constraints.map(con => linear(con.poly)).map(_._1).distinct
    // the non-basic variables are the monomials without their factors, such that products of atoms and powers are
    // variables of their own, about which nothing is known
    val atoms = constraints.flatMap(_.poly.monos.map(_.atoms)).distinct

    val n = atoms.length + rows.length
    // the coefficients of the non-basic variables in the rows of the basic ones, by index; atoms have the indices
    // 0 until atoms.length, the slacks those after
    val index = atoms.zipWithIndex.toMap
    val lower = Array.fill[Option[Delta]](n)(None)
    val upper = Array.fill[Option[Delta]](n)(None)
    val value = Array.fill(n)(Delta.zero)

    // the tableau as a map from basic variables to their rows, a row is a map from non-basic variables to coefficients
    val tableau = scala.collection.mutable.Map[Int, scala.collection.mutable.Map[Int, Rational]]()
    for (row, i) <- rows.zipWithIndex
    do
      val coeffs = scala.collection.mutable.Map[Int, Rational]()
      for Mono(factor, atoms_) <- row.monos
      do coeffs(index(atoms_)) = coeffs.getOrElse(index(atoms_), Rational(0)) + factor
      tableau(atoms.length + i) = coeffs

    val slack = rows.zipWithIndex.toMap

    def tighten(lo: Option[Delta], bound: Delta, isLower: Boolean): Option[Delta] =
      lo match
        case None                           => Some(bound)
        case Some(old) if isLower && old < bound  => Some(bound)
        case Some(old) if !isLower && bound < old => Some(bound)
        case _                              => lo

    for con <- constraints
    do
      val (lin, negated) = linear(con.poly)
      val s = atoms.length + slack(lin)
      val delta = if con.strict then Rational(1) else Rational(0)
      if !negated
      then lower(s) = tighten(lower(s), Delta(-con.poly.const, delta), true)
      else upper(s) = tighten(upper(s), Delta(con.poly.const, -delta), false)

    // a lower bound above the upper bound of a variable is a conflict on its own; otherwise the non-basic variables,
    // initially the atoms without bounds, satisfy their bounds throughout, since a basic variable leaves the basis at
    // the bound it violated, which is within its bounds
    val conflict = (0 until n).exists(x => (lower(x), upper(x)) match
      case (Some(lo), Some(hi)) => hi < lo
      case _                    => false)

    // the value of a basic variable from the values of the non-basic ones
    def recompute(x: Int): Unit =
      value(x) = tableau(x).foldLeft(Delta.zero) { case (acc, (y, a)) => acc + value(y) * a }

    for x <- tableau.keys do recompute(x)

    // the basic variable x leaves the basis, the non-basic y enters: x = ... + a y + ... is solved for y and substituted
    def pivot(x: Int, y: Int): Unit =
      val row = tableau.remove(x).get
      val a = row(y)
      val rowy = scala.collection.mutable.Map[Int, Rational]()
      for (z, b) <- row if z != y do rowy(z) = -b / a
      rowy(x) = Rational(1) / a
      for (z, r) <- tableau if r.contains(y)
      do
        val c = r.remove(y).get
        for (w, b) <- rowy
        do
          val b_ = r.getOrElse(w, Rational(0)) + c * b
          if b_.isZero then r.remove(w) else r(w) = b_
      tableau(y) = rowy

    def violated(x: Int): Boolean =
      lower(x).exists(value(x) < _) || upper(x).exists(_ < value(x))

    // x is basic and violates a bound: a non-basic variable y of its row that can move x towards the bound, pivoted
    // and set such that x takes the bound; Bland's rule chooses the smallest indices, which terminates
    def check(): Boolean =
      var sat = false
      var done = false
      while !done do
        val xs = tableau.keys.filter(violated).toList.sorted
        xs match
          case Nil =>
            done = true
            sat = true

          case x :: _ =>
            val row = tableau(x)
            val toLower = lower(x).exists(value(x) < _)
            val target = if toLower then lower(x).get else upper(x).get
            val candidates =
              for
                (y, a) <- row.toList.sortBy(_._1)
                // increase x: y with positive coefficient may increase (below upper), negative may decrease (above lower)
                ok =
                  if toLower
                  then (a.isPositive && upper(y).forall(value(y) < _)) || (a.isNegative && lower(y).forall(_ < value(y)))
                  else (a.isPositive && lower(y).forall(_ < value(y))) || (a.isNegative && upper(y).forall(value(y) < _))
                if ok
              yield y
            candidates match
              case Nil =>
                done = true
                sat = false

              // x takes its bound and y moves accordingly, then y enters the basis in place of x, and the values of
              // the basic variables follow from the non-basic ones, among them now x
              case y :: _ =>
                val a = row(y)
                val theta = (target - value(x)) * (Rational(1) / a)
                value(x) = target
                value(y) = value(y) + theta
                pivot(x, y)
                for z <- tableau.keys do recompute(z)

      sat

    !conflict && check()
