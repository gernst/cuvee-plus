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

// the verdicts of the programs simplified statement by statement are checked by transform.Verdicts
