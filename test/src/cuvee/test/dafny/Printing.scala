package cuvee.test
package dafny

import utest._

import cuvee.core._
import cuvee.dafny.Printer

object Printing extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val zero = Lit(BigInt(0), Sort.int)
  val p = Var("p", Sort.bool)
  val q = Var("q", Sort.bool)

  // the printer ignores types, chains with more than two arguments do not match the signatures
  def app(fun: Fun, args: Expr*) =
    App(fun, Nil, fun.res, args.toList)

  def expr(expr: Expr) =
    Printer.lines(expr).mkString(" ")

  val tests = Tests:
    test("assign"):
      Printer.lines(Assign(List(x, y), List(y, x))) ==> List("x, y := y, x;")

    test("specs"):
      Printer.lines(Spec.assume(App(Fun.int.lt, List(x, y)))) ==> List("assume x < y;")
      Printer.lines(Spec.havoc(List(x, y))) ==> List("havoc x, y;")
      Printer.lines(Spec(List(x), App(Fun.int.lt, List(zero, x)), App(Fun.int.lt, List(x, y)))) ==>
        List("spec x requires 0 < x ensures x < y;")

    test("choice"):
      val progs = List(Assign(List(x), List(zero)), Assign(List(x), List(y)))
      Printer.lines(Choice(progs)) ==> List("if * {", "  x := 0;", "} else {", "  x := y;", "}")

    test("else if"):
      val prog = If(App(Fun.int.lt, List(x, y)), Break, If(App(Fun.int.lt, List(y, x)), Continue, Block(Nil, Nil)))
      Printer.lines(prog) ==> List("if x < y {", "  break;", "} else if y < x {", "  continue;", "}")

    test("mixfix"):
      expr(app(Fun.int.plus, app(Fun.int.plus, x, y), zero)) ==> "x + y + 0"
      expr(app(Fun.int.plus, x, app(Fun.int.plus, y, zero))) ==> "x + (y + 0)"
      expr(app(Fun.int.plus, x, y, zero)) ==> "x + y + 0"
      expr(app(Fun.int.times, app(Fun.int.plus, x, y), app(Fun.int.minus, x, y))) ==> "(x + y) * (x - y)"
      expr(app(Fun.int.minus, x, app(Fun.int.times, y, Lit(BigInt(-1), Sort.int)))) ==> "x - y * -1"
      expr(app(Fun.imp, p, app(Fun.imp, q, p))) ==> "p ==> q ==> p"
      expr(app(Fun.imp, app(Fun.imp, p, q), p)) ==> "(p ==> q) ==> p"
      expr(app(Fun.and, app(Fun.or, p, q), app(Fun.int.lt, x, y))) ==> "(p || q) && x < y"

    test("mixfix non-associative"):
      expr(app(Fun.eq_, app(Fun.int.lt, x, y), p)) ==> "(x < y) == p"
      expr(app(Fun.eq_, p, app(Fun.eq_, q, p))) ==> "p == (q == p)"
      expr(app(Fun.eq_, x, y, zero)) ==> "==(x, y, 0)"

    test("mixfix prefix"):
      expr(app(Fun.not, app(Fun.and, p, q))) ==> "!(p && q)"
      expr(app(Fun.and, app(Fun.not, p), q)) ==> "!p && q"
      expr(app(Fun.eq_, app(Fun.not, p), q)) ==> "!p == q"
      expr(app(Fun.int.uminus, app(Fun.int.uminus, x))) ==> "-(-x)"
      expr(app(Fun.int.plus, app(Fun.int.uminus, x), y)) ==> "-x + y"

    test("mixfix binders"):
      val all = Bind("forall", List(x), app(Fun.int.lt, x, y))
      expr(app(Fun.and, all, p)) ==> "(forall x: int :: x < y) && p"

    test("long call breaks"):
      val args = List.fill(12)(Var("argument", Sort.int))
      val lines = Printer.lines(Call("procedure", args, List(x)))
      lines.head ==> "x := procedure("
      lines.last ==> "  argument);"
      assert(lines.forall(_.length <= Printer.width))
