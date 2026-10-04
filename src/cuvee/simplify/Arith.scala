package cuvee.simplify

import scala.math.Ordering.Implicits.seqOrdering
import util.Rational
import cuvee.Error
import cuvee.core._

// constant factor times a product of atoms with positive exponents;
// in normal form, each atom occurs at most once, in canonical order;
// the factors are rationals, which are integers as long as the expression is on Int
case class Mono(factor: Rational, atoms: List[(Expr, BigInt)]):
  def unary_- : Mono =
    Mono(-factor, atoms)

  def *(that: Rational): Mono =
    Mono(factor * that, atoms)

  // the atoms are not merged
  def *(that: Mono): Mono =
    Mono(factor * that.factor, atoms ++ that.atoms)

  // merge equal atoms by adding their exponents
  def normalize: Mono =
    val atoms_ =
      for (expr, group) <- atoms.groupBy(_._1).toList
      yield (expr, group.map(_._2).sum)
    Mono(factor, atoms_.sortBy(_._1))

  // exponents are expanded into repeated factors, a factor of 1 is omitted and -1 becomes a negation
  def toExpr(ring: Ring): Expr =
    val args =
      for (expr, exp) <- atoms; _ <- List.range(BigInt(0), exp)
      yield expr

    if factor == Rational(1) then ring.times(args)
    else if factor == Rational(-1) then ring.uminus(ring.times(args))
    else ring.times(ring.lit(factor) :: args)

object Mono:
  // compares the atoms only, so that monomials which differ in their factor can be merged
  given Ordering[Mono] = Ordering.by(_.atoms)

  // a non-arithmetic expression, e.g. a variable, as a monomial of degree 1
  def atom(expr: Expr) =
    Mono(Rational(1), List(expr -> BigInt(1)))

// constant offset plus a sum of monomials with at least one atom;
// in normal form, the factors are nonzero and
// monomials over the same atoms occur at most once, in canonical order
case class Poly(const: Rational, monos: List[Mono]):
  def unary_- : Poly =
    Poly(-const, monos.map(-_))

  // the monomials are not merged
  def +(that: Poly): Poly =
    Poly(const + that.const, monos ++ that.monos)

  def -(that: Poly): Poly =
    this + -that

  def *(that: Rational): Poly =
    Poly(const * that, monos.map(_ * that))

  // multiply out: (c + ms) * (d + ns) = c*d + ms*d + c*ns + ms*ns
  def *(that: Poly): Poly =
    val monos_ =
      for m <- monos; n <- that.monos
      yield m * n
    Poly(const * that.const, monos.map(_ * that.const) ++ that.monos.map(_ * const) ++ monos_)

  // normalize the monomials and merge those over the same atoms by adding their factors,
  // monomials without atoms are moved into the constant
  def normalize: Poly =
    val (consts, monos_) = monos.map(_.normalize).partition(_.atoms.isEmpty)
    val const_ = consts.map(_.factor).foldLeft(const)(_ + _)

    val merged =
      for (atoms, group) <- monos_.groupBy(_.atoms).toList
      yield Mono(group.map(_.factor).foldLeft(Rational(0))(_ + _), atoms)

    Poly(const_, merged.filter(!_.factor.isZero).sorted)

  // the parts with negative and with positive coefficients, negated and as they are,
  // i.e., (neg, pos) with this = pos - neg, where both have positive coefficients only
  def sides: (Poly, Poly) =
    val (pos, neg) = monos.partition(_.factor.isPositive)
    val (const_neg, const_pos) =
      if const.isNegative
      then (-const, Rational(0))
      else (Rational(0), const)
    (Poly(const_neg, neg.map(-_)), Poly(const_pos, pos))

  // print back in a canonical order, so that equal polynomials yield equal expressions
  // (required for the fixpoint check in Simplify.simplify)
  // a constant of 0 is omitted, it is placed last otherwise
  def toExpr(ring: Ring): Expr =
    val const_ =
      if const.isZero
      then Nil
      else List(ring.lit(const))

    ring.plus(monos.map(_.toExpr(ring)) ++ const_)

object Poly:
  val zero = const(Rational(0))
  val one = const(Rational(1))

  def const(n: Rational): Poly =
    Poly(n, Nil)

  def atom(expr: Expr): Poly =
    Poly(Rational(0), List(Mono.atom(expr)))

// the sugar of arithmetic on Int or Real, by which polynomials are read and printed back,
// where the integral coefficients on Int become integer literals
case class Ring(
    typ: Type,
    uminus: Sugar.unary,
    plus: Sugar.commutative,
    minus: Sugar.associative,
    times: Sugar.commutative,
    lit: Rational => Expr
):
  // the value of a literal of this type
  def num(expr: Expr): Option[Rational] =
    expr match
      case Lit(n: BigInt, `typ`)   => Some(Rational(n))
      case Lit(r: Rational, `typ`) => Some(r)
      case _                       => None

// the rings Int and Real, where the coefficients on Int must be integral
object Ring:
  val int =
    Ring(Sort.int, UMinus.int, Plus.int, Minus.int, Times.int, n =>
      Error.report("non-integral coefficient in integer arithmetic", n):
        require(n.den == 1)
      Lit(n.num, Sort.int))

  val real =
    Ring(Sort.real, UMinus.real, Plus.real, Minus.real, Times.real, r => Lit(r, Sort.real))

  // the ring of `typ`, if it is Int or Real
  def apply(typ: Type): Option[Ring] =
    if typ == Sort.int then Some(int)
    else if typ == Sort.real then Some(real)
    else None

  // the value of a literal on Int or Real
  def num(expr: Expr): Option[Rational] =
    int.num(expr) orElse real.num(expr)

// normal form of arithmetic on Int and Real as polynomials over atoms,
// where atoms are all subterms that are not built from +, -, * and literals,
// e.g. variables, applications of uninterpreted functions, div, mod, ite,
// and on Real, division by a nonzero literal, which is multiplication by its inverse
//
// example: (x + 1) * (x - 1)  ~>  x*x + -1
object Arith:
  // entry point for the simplifier:
  // normalize an arithmetic expression whose subterms are already simplified
  def normalize(ring: Ring, expr: Expr): Expr =
    toPoly(ring, expr).normalize.toExpr(ring)

  // interpret an expression as a polynomial, flattening sums and products
  def toPoly(ring: Ring, expr: Expr): Poly =
    ring.num(expr) match
      case Some(n) =>
        Poly.const(n)

      case None =>
        expr match
          case ring.uminus(arg)        => -toPoly(ring, arg)
          case ring.plus(args)         => args.map(toPoly(ring, _)).foldLeft(Poly.zero)(_ + _)
          case ring.minus(left, right) => toPoly(ring, left) - toPoly(ring, right)
          case ring.times(args)        => args.map(toPoly(ring, _)).foldLeft(Poly.one)(_ * _)
          case DivBy.real(left, Lit(r: Rational, _)) if ring == Ring.real && !r.isZero =>
            toPoly(ring, left) * (Rational(1) / r)
          case _ =>
            Poly.atom(expr)
