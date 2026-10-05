package cuvee.test
package boogie

import utest._

import cuvee.Error
import cuvee.core._

// Boogie examples must be resolved and type checked without errors
object Parsing extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "boogie", "bpl")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

// inputs that are rejected, in particular, global variables may be assigned and modified by calls
// only if they are declared as modified
object Errors extends TestSuite:
  def error(text: String): String =
    try
      cuvee.boogie.Source(new java.io.StringReader(text))._2.toList
      "no error"
    catch case Error(msg, _*) => msg

  val globals = "var g: int; var h: int; procedure set() modifies g; { g := 0; } "

  val tests = Tests:
    test("assignment to a global variable that is not modified"):
      val msg = error(globals + "procedure p() modifies h; { g := 1; }")
      assert(msg.contains("assign"))

    test("call that modifies a global variable that is not modified"):
      error(globals + "procedure p() modifies h; { call set(); }") ==>
        "call modifies variables that are not in the modifies clause"

    test("call inside a loop without modifies clause"):
      error(globals + "procedure p() modifies g; { while (true) { call set(); } }") ==>
        "call modifies variables that are not in the modifies clause"

    test("call inside a loop with modifies clause"):
      error(globals + "procedure p() modifies g; { while (true) modifies g; { call set(); } }") ==> "no error"

    test("loop modifies a global variable that is not modified"):
      error(globals + "procedure p() { while (true) modifies g; { } }") ==>
        "modifies clause of loop lists global variables that are not modifiable"

    test("modifies clause of a loop lists a local variable"):
      error(globals + "procedure p() { var x: int; while (true) modifies x; { } }") ==>
        "modifies clause of loop lists variables that are not global"

    test("modifies clause of a procedure lists a local variable"):
      error("procedure p(x: int) modifies x; { }") ==>
        "modifies clause of procedure lists variables that are not global"

    test("semicolon after the signature of a procedure without body"):
      error("procedure p() requires true;") ==> "parse error"

    test("no semicolon after the signature of a procedure with body"):
      error("procedure p(); { }") ==> "parse error"

    test("inputs are not modified"):
      val msg = error("procedure p(x: int) { x := 1; }")
      assert(msg.contains("assign"))

// string literals escape double quotes and backslashes, which print back the same way
object Strings extends TestSuite:
  val tests = Tests:
    test("escapes"):
      val text = "axiom \"a \\\"quoted\\\" \\\\ string\" == \"x\";"
      val file = os.temp(text, suffix = ".bpl")
      val (cmds, errors) = Examples.output("-print", "null", file.toString)
      errors ==> Nil
      val List(cuvee.core.Assert(_, _, cuvee.core.Eq(cuvee.core.Lit(value, _), _), _)) = cmds: @unchecked
      value ==> "a \"quoted\" \\ string"
      cuvee.boogie.Printer.lines(cmds.head).head ==> text
