package cuvee.test
package boogie

import utest._

import cuvee.Error
import cuvee.core._

// the examples in boogie, each with its command line in the first line, e.g. ./Cuvee.sh -verify -monomorph -z3 ...,
// where traces.bpl, whose combinators the solvers do not support, is printed only,
// and the examples of horn are for -chc only, their procedures with a body have no contracts
object Verify extends TestSuite:
  val tests =
    Examples.checked(os.sub / "boogie", "bpl")

// runs the examples with -chc against z3, which checks the clauses for satisfiability:
// sat if all queries hold, unsat if one of them fails
object Horn extends TestSuite:
  // the other examples are not covered, since their procedures with a body have contracts
  val tests =
    Examples.tests(Examples.find(os.sub / "boogie" / "horn", "bpl")): file =>
      Examples.show(List("-chc", "-monomorph", "-z3", file.toString))
      val (_, results) = cuvee.Cuvee.run("-chc", "-monomorph", "-z3", file.toString)
      results.collect { case error: Error => error.msg } ==> Nil
      Examples.status(results) ==> (if Examples.holds(file) then Status.Sat else Status.Unsat)

// global variables are eliminated by -verify and -chc, and are not passed to solvers
object Globals extends TestSuite:
  val globals = Examples.root / "boogie" / "globals.bpl"
  val horn = Examples.root / "boogie" / "horn" / "globals.bpl"

  def output(args: String*): List[Cmd] =
    val (cmds, errors) = Examples.output(args*)
    errors ==> Nil
    cmds

  val tests = Tests:
    test("declared"):
      val cmds = output("-print", "null", globals.toString)
      val vars = cmds.collect { case DeclareVar(x, _) => x.name.name }
      vars ==> List("counter", "limit")

    test("eliminated by -verify"):
      val cmds = output("-verify", "-print", "null", globals.toString)
      assert(!cmds.exists(_.isInstanceOf[DeclareVar]))

    test("eliminated by -chc"):
      val cmds = output("-chc", "-print", "null", horn.toString)
      assert(!cmds.exists(_.isInstanceOf[DeclareVar]))

    // the predicates range over the global variables, the postcondition also over their values at the entry
    test("arguments of the predicates"):
      val cmds = output("-chc", "-print", "null", horn.toString)
      val arity = cmds.collect { case DeclareFun(fun, _) => fun.name.name -> fun.arity }.toMap
      arity("incr_pre") ==> 2
      arity("incr_post") ==> 4

    test("unsupported by solvers"):
      val file = Examples.root / "boogie" / "parsing" / "unsupported.bpl"
      Examples.show(List("-z3", file.toString))
      val (_, results) = cuvee.Cuvee.run("-z3", file.toString)
      assert(results.contains(Ack.Unsupported))
