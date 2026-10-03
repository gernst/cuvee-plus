package cuvee.test

import utest._

import cuvee.core._
import cuvee.dafny.Printer

object DafnyPrinter extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val zero = Lit(BigInt(0), Sort.int)

  val tests = Tests:
    test("assign"):
      Printer.lines(Assign(List(x, y), List(y, x))) ==> List("x, y := y, x;")

    test("specs"):
      Printer.lines(Spec.assume(App(Fun.lt, List(x, y)))) ==> List("assume <(x, y);")
      Printer.lines(Spec.havoc(List(x, y))) ==> List("havoc x, y;")
      Printer.lines(Spec(List(x), App(Fun.lt, List(zero, x)), App(Fun.lt, List(x, y)))) ==>
        List("spec x requires <(0, x) ensures <(x, y);")

    test("choice"):
      val progs = List(Assign(List(x), List(zero)), Assign(List(x), List(y)))
      Printer.lines(Choice(progs)) ==> List("if * {", "  x := 0;", "} else {", "  x := y;", "}")

    test("else if"):
      val prog = If(App(Fun.lt, List(x, y)), Break, If(App(Fun.lt, List(y, x)), Continue, Block(Nil, Nil)))
      Printer.lines(prog) ==> List("if <(x, y) {", "  break;", "} else if <(y, x) {", "  continue;", "}")

    test("long call breaks"):
      val args = List.fill(12)(Var("argument", Sort.int))
      val lines = Printer.lines(Call("procedure", args, List(x)))
      lines.head ==> "x := procedure("
      lines.last ==> "  argument);"
      assert(lines.forall(_.length <= Printer.width))
