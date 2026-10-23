package cuvee.test

import utest._

// the examples of each language, below examples/<language>/<module>/, each a test of the command line
// in its first line (see Examples.checked and cuvee.test.Expected)
object Dafny extends TestSuite:
  val tests =
    Examples.checked(os.sub / "dafny", "dfy")

object Boogie extends TestSuite:
  val tests =
    Examples.checked(os.sub / "boogie", "bpl")

object C extends TestSuite:
  val tests =
    Examples.checked(os.sub / "c", "c")

object SmtLib extends TestSuite:
  val tests =
    Examples.checked(os.sub / "smtlib", "smt2")

object Yml extends TestSuite:
  val tests =
    Examples.checked(os.sub / "yml", "yml")

object SvLib extends TestSuite:
  val tests =
    Examples.checked(os.sub / "svlib", "svlib")
