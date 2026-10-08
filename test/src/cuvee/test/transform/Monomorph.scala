package cuvee.test
package transform

import utest._

import cuvee.core._

// polymorphic functions are replaced by their instances, which are declared before their first use,
// as the expected outputs of examples/transform/mono*.smt2 show; the instances are passed to the solver
object Monomorph extends TestSuite:
  val file = (Examples.root / "transform" / "mono.smt2").toString

  val tests = Tests:
    test("solver"):
      Examples.show(List("-monomorph", "-z3", file))
      val (_, results) = cuvee.Cuvee.run("-monomorph", "-z3", file)
      Examples.status(results) ==> Status.Sat
