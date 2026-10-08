package cuvee.test
package smtlib

import utest._

// the examples in simplify/, each with its command line in the first line, e.g. ./Cuvee.sh -simplify ...
object Simplify extends TestSuite:
  val tests =
    Examples.checked(List("smt2", "dfy", "bpl").flatMap(Examples.find(os.sub / "simplify", _)))

// derivatives (x, y :: e)' by the rules of dL, printed in Dafny syntax
object Derivatives extends TestSuite:
  import cuvee.core._
  import cuvee.simplify.Context
  import _root_.util.Rational

  val x = Var("x", Sort.real)
  val y = Var("y", Sort.real)
  val c = Var("c", Sort.real)
  val n = Var("n", Sort.int)
  val two = Lit(Rational(2), Sort.real)
  val f = Fun("f", Nil, List(Var("a", Sort.real)), Sort.real)

  def diff(expr: Expr, xs: Var*) =
    val expr_ = cuvee.simplify.Simplify.simplify(cuvee.Config.default, State.empty, Context.empty, Diff(xs.toList, expr))
    cuvee.dafny.Printer.lines(expr_).mkString(" ").replaceAll(" +", " ")

  val tests = Tests:
    test("constants"):
      diff(Plus.real(c, two), x) ==> "0.0"

    // derivatives are on Real only, the type checker rejects these, which are built directly
    test("integers"):
      diff(Times.int(n, n), n) ==> "(n :: n * n)'"
      diff(Lt.int(n, Zero.int), n) ==> "(n :: n < 0)'"

    test("variables"):
      diff(x, x) ==> "x'"
      diff(Plus.real(x, y), x, y) ==> "x' + y'"
      diff(Minus.real(x, c), x) ==> "x'"

    test("product rule"):
      diff(Times.real(x, y), x, y) ==> "x' * y + x * y'"
      diff(Times.real(c, x), x) ==> "c * x'"

    test("comparisons and conjunction"):
      diff(Lt.real(x, c), x) ==> "x' <= 0.0"
      diff(Eq(x, Times.real(c, y)), x, y) ==> "x' == c * y'"
      diff(And(Le.real(c, x), Lt.real(x, y)), x, y) ==> "0.0 <= x' <= y'"

    // the chain rule for other functions is not applied
    test("other functions"):
      diff(App(f, List(x)), x) ==> "(x :: f(x))'"

// programs are simplified statement by statement (see examples/simplify/statements.dfy),
// before verification the verdicts are the same
object SimplifyPrograms extends TestSuite:
  val tests = Tests:
    test("examples"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filter(Examples.supported)
      do Examples.errors("-simplify", "-verify", "-z3", file.toString) ==> Examples.reported(file)
