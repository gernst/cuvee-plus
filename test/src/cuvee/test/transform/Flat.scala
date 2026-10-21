package cuvee.test
package transform

import utest._

import cuvee.Error
import cuvee.core._
import cuvee.Cuvee

// the Horn clauses of the Dafny examples have the same result with -flat as without
object FlatHorn extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "dafny" / "horn", "dfy")): file =>
      val results = Examples.answers("-chc", "-entry", "main", "-flat", "-z3", file.toString)
      results.collect { case error: Error => error.msg } ==> Nil
      Examples.status(results) ==> (if Examples.holds(file) then Status.Sat else Status.Unsat)

// the transformation -flat on examples/smtlib/transform/flat*.smt2 is checked by their expected outputs,
// its errors by those of examples/smtlib/parsing/flat_*.smt2
object Flat extends TestSuite:
  val file = (Examples.root / "smtlib" / "transform" / "flat.smt2").toString

  val tests = Tests:
    test("satisfiable"):
      val results = Examples.answers("-flat", "-z3", file)
      Examples.status(results) ==> Status.Sat
