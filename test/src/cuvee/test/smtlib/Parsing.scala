package cuvee.test
package smtlib

import utest._

object Parsing extends TestSuite:
  // SMT-LIB examples must parse without errors
  val tests =
    Examples.tests(Examples.find(os.sub, "smt2")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

// a doubled "" inside a string stands for " (SMT-LIB 2.6)
object Strings extends TestSuite:
  import cuvee.core._

  val tests = Tests:
    test("escape"):
      val (_, cmds) = cuvee.smtlib.Source(new java.io.StringReader("(assert (= \"a\"\"b\" \"\"))"))
      val List(Assert(_, _, Eq(Lit(left, _), Lit(right, _)), _)) = cmds.toList: @unchecked
      (left, right) ==> ("a\"b", "")
      cuvee.smtlib.Printer.lines(Lit("a\"b", Sort.string)) ==> List("\"a\"\"b\"")
