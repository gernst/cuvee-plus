package cuvee.test
package transform

import utest._

import cuvee.Error
import cuvee.core._

// the Horn clauses of the Dafny examples have the same result with -flat as without
object FlatHorn extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "dafny" / "horn", "dfy")): file =>
      Examples.show(List("-chc", "-flat", "-z3", file.toString))
      val (_, results) = cuvee.Cuvee.run("-chc", "-flat", "-z3", file.toString)
      results.collect { case error: Error => error.msg } ==> Nil
      Examples.status(results) ==> (if Examples.holds(file) then Status.Sat else Status.Unsat)

// the transformation -flat on examples/transform/flat*.smt2 is checked by their expected outputs,
// its errors by those of examples/transform/parsing
object Flat extends TestSuite:
  val file = (Examples.root / "transform" / "flat.smt2").toString

  val tests = Tests:
    test("satisfiable"):
      Examples.show(List("-flat", "-z3", file))
      val (_, results) = cuvee.Cuvee.run("-flat", "-z3", file)
      Examples.status(results) ==> Status.Sat
