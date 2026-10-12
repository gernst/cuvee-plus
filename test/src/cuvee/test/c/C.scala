package cuvee.test
package c

import utest._

import cuvee.core._
import cuvee.Cuvee

// printing the C examples is stable after a first round of parsing and printing again
object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.printing(Examples.valid(os.sub / "c", "c"))): file =>
      Examples.roundtrip(file, Nil, rounds = 1)

// all examples with -chc whose second line states whether all assertions hold,
// except for division by variables, for which z3 answers unknown
object Horn extends TestSuite:
  val skip = Set("div.c")

  def stated(file: os.Path) =
    os.read.lines(file)(1).startsWith("// expected:")

  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c").filter(stated).filterNot(file => skip.contains(file.last))): file =>
      Examples.show(List("-simplify", "-chc", "-z3", file.toString))
      val (_, results) = Cuvee.run("-simplify", "-chc", "-z3", file.toString)
      Examples.status(results) ==> (if Examples.holds(file) then Status.Sat else Status.Unsat)

// the output is C: what is not C is printed in SMT-LIB as SMT_LIB(...), e.g. assertions and quantifiers,
// contracts are omitted (see also examples/c/printing)
object Printing extends TestSuite:
  val x = Var("x", Sort.int)
  val g = Var("g", Sort.int)
  val p = Fun("p", Nil, Fun.formals(Sort.int), Sort.bool)

  def print(cmd: Cmd) =
    cuvee.c.Printer.lines(cmd)

  val tests = Tests:
    test("assertions"):
      print(Assert(Axiom, Nil, All(List(x), Imp(App(p, List(x)), Ints.lt(x, Ints.one))), Attrs.empty)) ==>
        List("SMT_LIB((assert", "          (forall ((x Int)) (=> (p x) (< x 1)))))", "")

    test("declarations"):
      // functions are the logic functions and predicates of ACSL
      print(DeclareFun(p, Attrs.empty)) ==> List("/*@ predicate p(integer x_0); */", "")
      print(DefineFun(p, Ex(List(x), Ints.lt(x, Ints.one)), Attrs.empty)) ==>
        List("/*@ predicate p(integer x_0) = \\exists integer x; x < 1; */", "")
      print(CheckSat) ==> List("SMT_LIB((check-sat))", "")

    // models are not programs, they are SMT-LIB
    test("models"):
      val model = Model(List(DefineFun(p, Ints.lt(Var("x", Sort.int), Ints.one), Attrs.empty)))
      cuvee.c.Printer.lines(model) ==> cuvee.smtlib.Printer.lines(model)
