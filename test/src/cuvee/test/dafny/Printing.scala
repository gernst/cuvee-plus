package cuvee.test
package dafny

import utest._

import cuvee.core._
import cuvee.dafny.Printer

// the printer on terms that no input produces (see examples/dafny/printing and examples/smtlib/printing/dafny_*.smt2
// for the others)
object Printing extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val zero = Lit(BigInt(0), Sort.int)

  def expr(expr: Expr) =
    Printer.lines(expr).mkString(" ")

  val tests = Tests:
    // equations of more than two arguments do not match the signature, the parsers build chains instead
    test("mixfix non-associative"):
      expr(App(Fun.eq_, Nil, Sort.bool, List(x, y, zero))) ==> "==(x, y, 0)"

    // the definitions of a model are separated by empty lines, like commands, models come from solvers only
    test("model"):
      val f = Fun("f", Nil, List(x), Sort.int)
      val g = Fun("g", Nil, List(x), Sort.int)
      Printer.lines(Model(List(DefineFun(f, x, Attrs.empty), DefineFun(g, x, Attrs.empty)))).count(_.isEmpty) ==> 1
