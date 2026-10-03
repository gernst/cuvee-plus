package cuvee.test
package smtlib

import utest._

object Parsing extends TestSuite:
  // SMT-LIB examples must parse without errors
  val tests =
    Examples.tests(Examples.find(os.sub, "smt2")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil
