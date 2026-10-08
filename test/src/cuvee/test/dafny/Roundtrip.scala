package cuvee.test
package dafny

import utest._

// printing the Dafny examples is stable when the output is parsed again, the original file is not compared
object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.valid(os.sub / "dafny", "dfy")): file =>
      Examples.roundtrip(file, Examples.options(file))
