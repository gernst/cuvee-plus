package cuvee.test
package smtlib

import utest._

// runs the examples in simplify/ with -simplify,
// the expected output of each example `name.smt2` is given in `name.expected.smt2`
object Simplify extends TestSuite:
  val inputs =
    Examples.find(os.sub / "simplify", "smt2").filterNot(_.last.endsWith(".expected.smt2"))

  val tests =
    Examples.tests(inputs): file =>
      val expected = file / os.up / (file.baseName + ".expected.smt2")

      val (actual, errors) = Examples.output("-print", "null", "-simplify", file.toString)
      errors ==> Nil
      actual ==> Examples.input("-print", "null", expected.toString)

// derivatives (x, y :: e)' by the rules of dL, printed in Dafny syntax
object Derivatives extends TestSuite:
  import cuvee.core._
  import cuvee.simplify.Ctx
  import _root_.util.Rational

  val x = Var("x", Sort.real)
  val y = Var("y", Sort.real)
  val c = Var("c", Sort.real)
  val n = Var("n", Sort.int)
  val two = Lit(Rational(2), Sort.real)
  val f = Fun("f", Nil, List(Var("a", Sort.real)), Sort.real)

  def diff(expr: Expr, xs: Var*) =
    val expr_ = cuvee.simplify.Simplify.simplify(State.empty, Ctx.empty, Diff(xs.toList, expr))
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
      diff(And(Le.real(c, x), Lt.real(x, y)), x, y) ==> "0.0 <= x' && x' <= y'"

    // the chain rule for other functions is not applied
    test("other functions"):
      diff(App(f, List(x)), x) ==> "(x :: f(x))'"
