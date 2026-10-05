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
      val Assert(_, _, Eq(Lit(left, _), Lit(right, _)), _) = cmds.last: @unchecked
      (left, right) ==> ("a\"b", "")
      cuvee.smtlib.Printer.lines(Lit("a\"b", Sort.string)) ==> List("\"a\"\"b\"")

// bitvectors, whose functions are instantiated for the widths of their arguments
object BitVectors extends TestSuite:
  import cuvee.core._

  def expr(text: String): Expr =
    val (_, cmds) = cuvee.smtlib.Source(new java.io.StringReader("(declare-const x (_ BitVec 8))\n(assert (= " + text + " " + text + "))"))
    val Assert(_, _, Eq(left, _), _) = cmds.last: @unchecked
    left

  def errors(text: String) =
    val file = os.temp("(declare-const x (_ BitVec 8))\n(assert " + text + ")", suffix = ".smt2")
    Examples.errors("-print", "null", file.toString)

  val tests = Tests:
    test("literals"):
      expr("#xff") ==> Lit(BigInt(255), BitVec(8))
      expr("#b101") ==> Lit(BigInt(5), BitVec(3))
      expr("(_ bv5 16)") ==> Lit(BigInt(5), BitVec(16))

    test("widths"):
      expr("(concat x #b1)").typ ==> BitVec(9)
      expr("((_ extract 3 0) x)").typ ==> BitVec(4)
      expr("((_ repeat 3) x)").typ ==> BitVec(24)
      expr("(bvcomp x x)").typ ==> BitVec(1)

    test("errors"):
      errors("(= (bvadd x #b1) x)") ==> List("invalid application of bitvector function")
      errors("(= ((_ extract 8 0) x) x)") ==> List("invalid application of bitvector function")

    test("solver"):
      val file = Examples.root / "smtlib" / "bitvectors.smt2"
      val (_, results) = cuvee.Cuvee.run("-z3", file.toString)
      Examples.status(results) ==> Status.Unsat
