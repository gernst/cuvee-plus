package cuvee.test
package smtlib

import utest._

import cuvee.core._
import cuvee.smtlib.Printer

object Printing extends TestSuite:
  val x = Var("x", Sort.int)
  val f = Fun("f", Nil, List(x), Sort.int)
  val rw = Attrs(List("rw" -> None))

  def show(cmd: Cmd) =
    Printer.command(cmd).map(_.trim).mkString(" ")

  val tests = Tests:
    // SMT-LIB has no attributes on declarations and definitions, except as annotations of the formulas of assertions
    test("attributes"):
      show(DeclareFun(f, rw)) ==> "(declare-fun f (Int) Int)"
      show(DefineFun(f, x, rw)) ==> "(define-fun f ((x Int)) Int x)"
      show(DeclareSort(Con("S", 0), rw)) ==> "(declare-sort S 0)"
      show(Assert(Axiom, Nil, Eq(App(f, List(x)), x), rw)) ==> "(assert (! (= (f x) x) :rw))"
