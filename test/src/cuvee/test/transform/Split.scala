package cuvee.test
package transform

import utest._

// the obligations of -split hold if and only if the goals do, for the examples verified with -verify
// (see examples/smtlib/transform/split.smt2 for the obligations)
object Split extends TestSuite:
  val tests = Tests:
    test("examples"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filter(Examples.supported)
      do
        val errors = Examples.errors("-verify", "-split", "-z3", file.toString)
        if Examples.reported(file).isEmpty
        then assert(errors.isEmpty)
        else assert(errors.nonEmpty && errors.forall(_ == "goal does not hold"))
