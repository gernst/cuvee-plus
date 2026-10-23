package cuvee.test
package transform

import utest._

// the verdicts of the examples verified with -vcgen do not change by -split, some obligation of which is refuted if and
// only if a goal is (see examples/smtlib/transform/split.smt2 for the obligations), nor by -simplify, which simplifies
// programs statement by statement (see examples/dafny/simplify/statements.dfy); each example is verified once as is
object Verdicts extends TestSuite:
  val tests = Tests:
    test("examples"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filter(Examples.supported)
      do
        val refuted = Examples.answers("-vcgen", "-z3", file.toString).contains(cuvee.core.Status.Incorrect)
        Examples.answers("-vcgen", "-split", "-z3", file.toString).contains(cuvee.core.Status.Incorrect) ==> refuted
        Examples.answers("-simplify", "-vcgen", "-z3", file.toString).contains(cuvee.core.Status.Incorrect) ==> refuted
