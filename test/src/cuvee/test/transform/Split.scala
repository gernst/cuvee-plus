package cuvee.test
package transform

import utest._

// some obligation of -split is refuted if and only if a goal is, for the examples verified with -vcgen
// (see examples/smtlib/transform/split.smt2 for the obligations)
object Split extends TestSuite:
  val tests = Tests:
    test("examples"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filter(Examples.supported)
      do
        val refuted = Examples.answers("-vcgen", "-z3", file.toString).contains(cuvee.core.Status.Incorrect)
        Examples.answers("-vcgen", "-split", "-z3", file.toString).contains(cuvee.core.Status.Incorrect) ==> refuted
