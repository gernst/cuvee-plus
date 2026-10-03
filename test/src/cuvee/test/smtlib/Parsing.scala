package cuvee.test
package smtlib

import utest._

object Parsing extends TestSuite:
  // SMT-LIB examples must parse without errors,
  // and printing must be stable when the output is parsed again
  val tests =
    Examples.tests(Examples.find(os.sub, "smt2")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

      val first = os.temp(suffix = ".smt2")
      val second = os.temp(suffix = ".smt2")

      Examples.errors(file.toString, "-o", first.toString) ==> Nil
      Examples.errors(first.toString, "-o", second.toString) ==> Nil
      os.read(second) ==> os.read(first)
