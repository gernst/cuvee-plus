package cuvee.test
package dafny

import utest._

object Roundtrip extends TestSuite:
  // printing Dafny examples must be stable when the output is parsed again
  val tests =
    Examples.tests(Examples.find(os.sub, "dfy")): file =>
      val first = os.temp(suffix = ".dfy")
      val second = os.temp(suffix = ".dfy")

      Examples.errors(file.toString, "-o", first.toString) ==> Nil
      Examples.errors(first.toString, "-o", second.toString) ==> Nil
      os.read(second) ==> os.read(first)
