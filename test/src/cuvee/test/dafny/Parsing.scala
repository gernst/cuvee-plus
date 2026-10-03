package cuvee.test
package dafny

import utest._

object Parsing extends TestSuite:
  // Dafny examples must parse without errors
  val tests =
    Examples.tests(Examples.find(os.sub, "dfy")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil
