package cuvee.test
package c

import utest._

import cuvee.core._

// the C examples parse and print back to the same program, including division and remainder
object Parsing extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c")): file =>
      val first = os.temp(suffix = ".c")
      val second = os.temp(suffix = ".c")

      Examples.errors(file.toString, "-o", first.toString) ==> Nil
      Examples.errors(first.toString, "-o", second.toString) ==> Nil
      val third = os.temp(suffix = ".c")
      Examples.errors(second.toString, "-o", third.toString) ==> Nil
      os.read(third) ==> os.read(second)

// the examples without loops are verified with -verify, since C has no loop invariants,
// and all examples with -chc, except for division by variables, for which z3 answers unknown;
// the first line of each example states whether all assertions hold
object Verify extends TestSuite:
  def loops(file: os.Path) =
    List("while", "for", "do").exists(os.read(file).contains)

  def expected(file: os.Path) =
    os.read.lines(file).head match
      case "// expected: valid"   => true
      case "// expected: invalid" => false

  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c").filterNot(loops)): file =>
      val errors = Examples.errors("-verify", "-z3", file.toString)
      errors ==> (if expected(file) then Nil else List("goal does not hold"))

object Horn extends TestSuite:
  val skip = Set("div.c")

  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c").filterNot(file => skip.contains(file.last))): file =>
      val (_, results) = cuvee.Cuvee.run("-chc", "-z3", file.toString)
      Examples.status(results) ==> (if Verify.expected(file) then Status.Sat else Status.Unsat)

// the translation of C: conversions between integers and truth values, the inferred modifies attributes,
// and the constructs that are rejected
object Translation extends TestSuite:
  def parse(text: String) =
    cuvee.c.Source(new java.io.StringReader(text))._2.toList

  def errors(text: String) =
    val file = os.temp(text, suffix = ".c")
    Examples.errors("-print", "null", file.toString)

  def modifies(cmds: List[Cmd], name: String) =
    cmds.collectFirst:
      case DefineProc(Proc(_root_.util.Name(`name`, None), _, _, _), _, attrs) => attrs.modifies.map(_.name.name)

  val tests = Tests:
    test("modifies"):
      val cmds = parse("int g; int h; void f(void) { g = 1; } void k(void) { int h; h = 2; f(); } void m(void) { k(); }")
      modifies(cmds, "f") ==> Some(List("g"))
      modifies(cmds, "k") ==> Some(List("g"))
      modifies(cmds, "m") ==> Some(List("g"))

    test("conditions"):
      errors("int f(int x) { if (x) return !x; else return x && 1; }") ==> Nil

    test("calls in conditions"):
      errors("int f(int x); int g(int x) { return x && f(x); }") ==>
        List("calls in the right operand of && and || are not supported")

    // the initial values are the precondition of main, they must not call functions
    test("initialized globals"):
      errors("int g = 1; int main(void) { return g; }") ==> Nil
      errors("int f(void); int g = f();") ==> List("initial value of global variable must not call functions")
      errors("int a[2] = 1;") ==> List("initialized global array")

    test("unknown variable"):
      errors("int f(void) { return y; }") ==> List("unknown variable")

// formulas that are not C are written in a notation after ACSL
object Annotations extends TestSuite:
  val x = Var("x", Sort.int)
  val p = Fun("p", Nil, Fun.formals(Sort.int), Sort.bool)

  val tests = Tests:
    test("quantifiers"):
      val phi = All(List(x), Imp(App(p, List(x)), Lt.int(x, One.int)))
      cuvee.c.Printer.lines(Assert(Axiom, Nil, phi, Attrs.empty)) ==> List("/*@ axiom \\forall int x; p(x) ==> x < 1; */", "")

    test("declarations"):
      cuvee.c.Printer.lines(DeclareFun(p, Attrs.empty)) ==> List("_Bool p(int x_0);", "")
