package cuvee.simplify

import scala.math.Ordering.Implicits.seqOrdering
import cuvee.core._

// constant factor times a product of atoms with positive exponents;
// in normal form, each atom occurs at most once, in canonical order
case class Mono(factor: BigInt, atoms: List[(Expr, BigInt)]):
  def unary_- : Mono =
    Mono(-factor, atoms)

  def *(that: BigInt): Mono =
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
  def toExpr: Expr =
    val args =
      for (expr, exp) <- atoms; _ <- List.range(BigInt(0), exp)
      yield expr

    if factor == 1 then Times.int(args)
    else if factor == -1 then UMinus.int(Times.int(args))
    else Times.int(Lit(factor, Sort.int) :: args)

object Mono:
  // compares the atoms only, so that monomials which differ in their factor can be merged
  given Ordering[Mono] = Ordering.by(_.atoms)

  def atom(expr: Expr) =
    Mono(1, List(expr -> BigInt(1)))

// constant offset plus a sum of monomials with at least one atom;
// in normal form, the factors are nonzero and
// monomials over the same atoms occur at most once, in canonical order
case class Poly(const: BigInt, monos: List[Mono]):
  def unary_- : Poly =
    Poly(-const, monos.map(-_))

  // the monomials are not merged
  def +(that: Poly): Poly =
    Poly(const + that.const, monos ++ that.monos)

  def -(that: Poly): Poly =
    this + -that

  def *(that: BigInt): Poly =
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
    val const_ = const + consts.map(_.factor).sum

    val merged =
      for (atoms, group) <- monos_.groupBy(_.atoms).toList
      yield Mono(group.map(_.factor).sum, atoms)

    Poly(const_, merged.filter(_.factor != 0).sorted)

  // print back in a canonical order, so that equal polynomials yield equal expressions
  // (required for the fixpoint check in Simplify.simplify)
  // a constant of 0 is omitted, it is placed last otherwise
  def toExpr: Expr =
    val const_ =
      if const == 0
      then Nil
      else List(Lit(const, Sort.int))

    Plus.int(monos.map(_.toExpr) ++ const_)

object Poly:
  val zero = const(0)
  val one = const(1)

  def const(n: BigInt): Poly =
    Poly(n, Nil)

  def atom(expr: Expr): Poly =
    Poly(0, List(Mono.atom(expr)))

// normal form of integer arithmetic as polynomials over atoms,
// where atoms are all subterms that are not built from +, -, * and integer literals,
// e.g. variables, applications of uninterpreted functions, div, mod, ite
//
// example: (x + 1) * (x - 1)  ~>  x*x + -1
object Arith:
  // entry point for the simplifier:
  // normalize an arithmetic expression whose subterms are already simplified
  def normalize(expr: Expr): Expr =
    toPoly(expr).normalize.toExpr

  // interpret an expression as a polynomial, flattening sums and products
  def toPoly(expr: Expr): Poly =
    expr match
      case Lit(n: BigInt, Sort.int) => Poly.const(n)
      case UMinus.int(arg)          => -toPoly(arg)
      case Plus.int(args)           => args.map(toPoly).foldLeft(Poly.zero)(_ + _)
      case Minus.int(left, right)   => toPoly(left) - toPoly(right)
      case Times.int(args)          => args.map(toPoly).foldLeft(Poly.one)(_ * _)
      case _                        => Poly.atom(expr)
