package cuvee.simplify

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

  // scaled by a positive factor such that all coefficients, including the constant, are integers without
  // a common divisor; this preserves the sign and hence comparisons with 0, but not the value
  def primitive: Poly =
    val factors = const :: monos.map(_.factor)
    val lcm = factors.map(_.den).foldLeft(BigInt(1))((a, b) => a * b / a.gcd(b))
    val gcd = factors.map(r => (r * Rational(lcm)).num).foldLeft(BigInt(0))(_ gcd _)
    if gcd == 0 then this else this * Rational(lcm, gcd)

  // on Int, 0 <= p is 0 <= q + floor(c / g), where p = g * q + c and g is the gcd of the coefficients of the monomials,
  // e.g. 0 <= 51 - 2 * n is 0 <= 25 - n; the coefficients and the constant are integers on Int
  def floor: Poly =
    val g = monos.map(_.factor.num).foldLeft(BigInt(0))(_ gcd _)
    if g <= 1
    then this
    else Poly(Rational(const.num - (const.num mod g)) * Rational(1, g), monos.map(_ * Rational(1, g)))

  // the coefficients and the constant modulo n, between 0 and |n|, where monomials with coefficient 0 vanish;
  // equal modulo n, e.g. for (p mod n) on Int
  def modulo(n: BigInt): Poly =
    def mod(r: Rational) = Rational(r.num mod n.abs)
    Poly(mod(normalize.const), normalize.monos.map(m => Mono(mod(m.factor), m.atoms))).normalize

  // the first variable x with coefficient 1 or -1 that is `admissible`, together with the solution of this == 0 for x,
  // which does not contain x, e.g. n + x - 40 for x is 40 - n; in the order of the monomials,
  // which is canonical for normalized polynomials
  def solution(admissible: Var => Boolean): Option[(Var, Poly)] =
    val solutions =
      for
        mono <- monos.iterator
        x <- mono.atoms match
          case List((x: Var, e)) if e == 1 => List(x)
          case _                           => Nil
        if admissible(x) && (mono.factor == Rational(1) || mono.factor == Rational(-1))
        rest = Poly(const, monos.filterNot(_ == mono)) * (-mono.factor)
        if !rest.monos.exists(_.atoms.exists((atom, _) => atom.free contains x))
      yield (x, rest)
    solutions.nextOption()

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
    zero: Expr,
    num: Sugar.lit,
    uminus: Sugar.unary,
    plus: Sugar.commutative,
    minus: Sugar.associative,
    times: Sugar.commutative,
    lit: Rational => Expr
)

// the rings Int and Real, where the coefficients on Int must be integral
object Ring:
  val int =
    Ring(Sort.int, Zero.int, Num.int, UMinus.int, Plus.int, Minus.int, Times.int, n => Lit(n.toBigInt, Sort.int))

  val real =
    Ring(Sort.real, Zero.real, Num.real, UMinus.real, Plus.real, Minus.real, Times.real, r => Lit(r, Sort.real))

  // the ring of `typ`, if it is Int or Real
  def apply(typ: Type): Option[Ring] =
    typ match
      case Sort.int  => Some(int)
      case Sort.real => Some(real)
      case _         => None

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
    expr match
      case ring.num(n: BigInt)     => Poly.const(Rational(n))
      case ring.num(n: Rational)   => Poly.const(n)
      case ring.uminus(arg)        => -toPoly(ring, arg)
      case ring.plus(args)         => args.map(toPoly(ring, _)).foldLeft(Poly.zero)(_ + _)
      case ring.minus(left, right) => toPoly(ring, left) - toPoly(ring, right)
      case ring.times(args)        => args.map(toPoly(ring, _)).foldLeft(Poly.one)(_ * _)

      case DivBy.real(left, Lit(r: Rational, _)) if ring == Ring.real && !r.isZero =>
        toPoly(ring, left) * (Rational(1) / r)

      case _ =>
        Poly.atom(expr)
