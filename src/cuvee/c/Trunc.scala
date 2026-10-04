package cuvee.c

import cuvee.core._

// C's division and remainder, which truncate towards zero, in terms of div and mod of SMT-LIB,
// where the quotient is rounded towards negative infinity for a positive divisor, a = b * (a div b) + (a mod b) with 0 <= a mod b;
// the parser translates / and % by these, and the printer recognizes them to print / and % again
object Quot:
  def apply(a: Expr, b: Expr): Expr =
    val pos = Ite(Le.int(Zero.int, b), DivBy.int(a, b), UMinus.int(DivBy.int(a, UMinus.int(b))))
    val neg = Ite(Le.int(Zero.int, b), UMinus.int(DivBy.int(UMinus.int(a), b)), DivBy.int(UMinus.int(a), UMinus.int(b)))
    Ite(Le.int(Zero.int, a), pos, neg)

  def unapply(expr: Expr): Option[(Expr, Expr)] =
    expr match
      case Ite(Le.int(Zero.int, a), Ite(Le.int(Zero.int, b), _, _), _) if expr == Quot(a, b) =>
        Some((a, b))

      case _ =>
        None

object Rem:
  def apply(a: Expr, b: Expr): Expr =
    Minus.int(a, Times.int(b, Quot(a, b)))

  def unapply(expr: Expr): Option[(Expr, Expr)] =
    expr match
      case Minus.int(a, App(_, _, _, List(b, _))) if expr == Rem(a, b) =>
        Some((a, b))

      case _ =>
        None

// the operators / and % of C as functions, which occur only in the printer
object Trunc:
  val quot = Fun("/", Nil, Fun.formals(Sort.int, Sort.int), Sort.int)
  val rem = Fun("%", Nil, Fun.formals(Sort.int, Sort.int), Sort.int)

  // a mod b = a % b if that is nonnegative, otherwise a % b + |b|
  def mod(a: Expr, b: Expr): Expr =
    val r = App(rem, List(a, b))
    Ite(Le.int(Zero.int, r), r, Ite(Le.int(Zero.int, b), Plus.int(r, b), Minus.int(r, b)))

  // a div b = (a - a mod b) / b, where the division is exact
  def div(a: Expr, b: Expr): Expr =
    App(quot, List(Minus.int(a, mod(a, b)), b))
