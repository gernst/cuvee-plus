package cuvee.test
package smtlib

import utest._

// derivatives (x, y :: e)' by the rules of dL, printed in Dafny syntax
object Derivatives extends TestSuite:
  import cuvee.core._
  import cuvee.simplify.Context

  val n = Var("n", Sort.int)

  def diff(expr: Expr, xs: Var*) =
    val expr_ = cuvee.simplify.Simplify.simplify(cuvee.Config.default, State.empty, Context.empty, Diff(xs.toList, expr))
    cuvee.dafny.Printer.lines(expr_).mkString(" ").replaceAll(" +", " ")

  val tests = Tests:
    // derivatives are on Real only, the type checker rejects these, which are built directly
    // (see examples/dafny/simplify/derivatives.dfy for the others)
    test("integers"):
      diff(Ints.times(n, n), n) ==> "(n :: n * n)'"
      diff(Ints.lt(n, Ints.zero), n) ==> "(n :: n < 0)'"

// programs are simplified statement by statement (see examples/dafny/simplify/statements.dfy),
// before verification the verdicts are the same
object SimplifyPrograms extends TestSuite:
  val tests = Tests:
    test("examples"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filter(Examples.supported)
      do
        val refuted = Examples.answers("-vcgen", "-z3", file.toString).contains(cuvee.core.Status.Incorrect)
        Examples.answers("-simplify", "-vcgen", "-z3", file.toString).contains(cuvee.core.Status.Incorrect) ==> refuted
