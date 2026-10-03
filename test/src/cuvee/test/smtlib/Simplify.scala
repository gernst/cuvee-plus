package cuvee.test
package smtlib

import utest._

// runs the examples in simplify/ with -simplify,
// the expected output of each example `name.smt2` is given in `name.expected.smt2`
object Simplify extends TestSuite:
  val inputs =
    Examples.find(os.sub / "simplify", "smt2").filterNot(_.last.endsWith(".expected.smt2"))

  val tests =
    Examples.tests(inputs): file =>
      val expected = file / os.up / (file.baseName + ".expected.smt2")

      val (actual, errors) = Examples.output("-print", "null", "-simplify", file.toString)
      errors ==> Nil
      actual ==> Examples.input("-print", "null", expected.toString)
