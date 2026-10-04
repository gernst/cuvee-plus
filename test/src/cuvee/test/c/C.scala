package cuvee.test
package c

import utest._

import cuvee.core._

// the C examples parse, and those without division print back to the same program,
// since div and mod of SMT-LIB are printed as calls
object Parsing extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

object Roundtrip extends TestSuite:
  def plain(file: os.Path) =
    val code = os.read.lines(file).filterNot(_.trim.startsWith("//"))
    !code.exists(line => line.contains(" / ") || line.contains("%"))

  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c").filter(plain)): file =>
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

    test("initialized globals"):
      errors("int g = 1;") ==> List("initialized global variables are not supported")

    test("unknown variable"):
      errors("int f(void) { return y; }") ==> List("unknown variable")
