package cuvee.test
package transform

import utest._

import cuvee.core._
import cuvee.Cuvee

// polymorphic functions are replaced by their instances, which are declared before their first use,
// as the expected outputs of examples/smtlib/transform/mono*.smt2 show; the instances are passed to the solver
object Monomorph extends TestSuite:
  val file = (Examples.root / "smtlib" / "transform" / "mono.smt2").toString

  val tests = Tests:
    test("solver"):
      val results = Examples.answers("-monomorph", "-z3", file)
      Examples.status(results) ==> Status.Sat
