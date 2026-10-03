package cuvee.test
package dafny

import utest._

// runs the examples with -verify against z3,
// the first line of each example states whether all goals are valid:
//   "// expected: valid" or "// expected: invalid"
object Verify extends TestSuite:
  // errors reported for each expected result
  val expected = Map(
    "// expected: valid" -> Nil,
    "// expected: invalid" -> List("goal does not hold")
  )

  val tests =
    Examples.tests(Examples.find(os.sub / "vcgen", "dfy")): file =>
      val first = os.read.lines(file).head
      assert(expected.contains(first))

      Examples.errors("-verify", "-z3", file.toString) ==> expected(first)
