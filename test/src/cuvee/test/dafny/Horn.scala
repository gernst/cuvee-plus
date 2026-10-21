package cuvee.test
package dafny

import utest._

import cuvee.Error
import cuvee.core._
import cuvee.Cuvee

// runs the examples with -chc against z3, which checks the clauses for satisfiability:
// sat if all queries hold, unsat if one of them fails,
// the expected result is given by the second line of each example, after its command line;
// the examples of vcgen are not covered, since their procedures with a body have contracts
object Horn extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "dafny" / "horn", "dfy")): file =>
      // the answer to the check-sat at the end is the last result
      val results = Examples.answers("-chc", "-entry", "main", "-z3", file.toString)
      results.collect { case error: Error => error.msg } ==> Nil
      Examples.status(results) ==> (if Examples.holds(file) then Status.Sat else Status.Unsat)

// the models of -chc (the commands are those of the examples in dafny/horn and dafny/parsing/horn_*.dfy)
object HornCmds extends TestSuite:
  val tests = Tests:
    // the model of the predicates is read back from the solver and printed in the language of the input
    test("model"):
      val max = Examples.root / "dafny" / "horn" / "max.dfy"
      val List(Status.Sat, Model(decls)) = Examples.answers("-chc", "-entry", "main", "-z3", max.toString): @unchecked
      assert(decls.nonEmpty && decls.forall(_.isInstanceOf[DefineFun]))
      assert(cuvee.dafny.Printer.lines(Model(decls)).exists(_.startsWith("function max_")))

    // no model if the clauses are unsatisfiable
    test("no model"):
      val invalid = Examples.root / "dafny" / "horn" / "invalid_max.dfy"
      Examples.answers("-chc", "-entry", "main", "-z3", invalid.toString) ==> List(Status.Unsat)
