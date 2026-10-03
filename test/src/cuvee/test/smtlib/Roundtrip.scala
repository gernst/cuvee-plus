package cuvee.test
package smtlib

import utest._

object Roundtrip extends TestSuite:
  // printing SMT-LIB examples must be stable when the output is parsed again
  val tests =
    Examples.tests(Examples.find(os.sub, "smt2")): file =>
      val first = os.temp(suffix = ".smt2")
      val second = os.temp(suffix = ".smt2")

      Examples.errors(file.toString, "-o", first.toString) ==> Nil
      Examples.errors(first.toString, "-o", second.toString) ==> Nil
      os.read(second) ==> os.read(first)
