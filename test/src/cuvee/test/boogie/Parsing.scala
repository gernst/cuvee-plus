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

// the declarations of the prelude coincide with the builtin functions,
// such that the sugar of the core, e.g. Plus, applies to Boogie input
object Prelude extends TestSuite:
  val tests = Tests:
    test("builtins"):
      val (init, _) = cuvee.boogie.Source(new java.io.StringReader(""))
      val builtins = List(Fun.true_, Fun.false_, Fun.eq_, Fun.ite, Fun.select, Fun.store, Fun.not, Fun.and, Fun.or, Fun.imp, Fun.int.div, Fun.int.mod, Fun.real.div)

      for fun <- builtins
      do init.funs((fun.name, fun.arity)) ==> fun

    // arithmetic and comparison are generic, they are resolved after type checking
    test("overloaded"):
      val (init, _) = cuvee.boogie.Source(new java.io.StringReader(""))

      for fun <- List(Fun.int.uminus, Fun.int.plus, Fun.int.minus, Fun.int.times, Fun.int.lt, Fun.int.le, Fun.int.gt, Fun.int.ge)
      do assert(Overload.isGeneric(init.funs((fun.name, fun.arity))))

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
