package cuvee.simplify

import util.Rational
import cuvee.Error
import cuvee.core._

// a linear constraint 0 <= poly, or 0 < poly if strict, over the rationals,
// where the polynomial is normalized and its monomials are linear in the atoms, e.g. variables
case class Constraint(poly: Poly, strict: Boolean):
  // the coefficient of atom x, which is zero if x does not occur
  def coeff(x: Expr): Rational =
    poly.monos.collectFirst { case Mono(factor, List((`x`, n))) if n == 1 => factor }.getOrElse(Rational(0))

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

// Fourier-Motzkin elimination of atoms from a conjunction of linear constraints over the rationals,
// e.g. for Real, which is complete for satisfiability over the rationals, but not over the integers;
// not connected to the simplifier yet
object FourierMotzkin:
  def linear(c: Constraint): Boolean =
    c.poly.monos.forall:
      case Mono(_, List((_, n))) => n == 1
      case _                     => false

  // a constraint without x that follows from the constraints l and u with positive and negative coefficients of x:
  // with a > 0 and b < 0 the coefficients in 0 <= a x + p and 0 <= b x + q,
  // the combination -b (a x + p) + a (b x + q) = -b p + a q does not contain x
  def combine(x: Expr, l: Constraint, u: Constraint): Constraint =
    val a = l.coeff(x)
    val b = u.coeff(x)
    val poly = (l.poly * (-b) + u.poly * a).normalize
    Constraint(poly, l.strict || u.strict)

  // the constraints without x that are satisfiable iff `cs` is for some value of x,
  // constraints without atoms that hold are dropped
  def eliminate(x: Expr, cs: List[Constraint]): List[Constraint] =
    Error.report("constraints are not linear", cs):
      require(cs.forall(linear))

    val (lower, rest) = cs.partition(_.coeff(x).isPositive)
    val (upper, other) = rest.partition(_.coeff(x).isNegative)

    val combined =
      for l <- lower; u <- upper
      yield combine(x, l, u)

    (other ++ combined).filterNot(_.holds == Some(true)).distinct

  def eliminate(xs: List[Expr], cs: List[Constraint]): List[Constraint] =
    xs.foldLeft(cs)((cs, x) => eliminate(x, cs))

  // the constraints are satisfiable over the rationals iff no constant constraint fails after eliminating all atoms
  def satisfiable(cs: List[Constraint]): Boolean =
    val atoms = cs.flatMap(_.atoms).distinct
    eliminate(atoms, cs).forall(_.holds != Some(false))
