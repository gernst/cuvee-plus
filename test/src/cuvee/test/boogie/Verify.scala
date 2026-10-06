package cuvee.test
package boogie

import utest._

import cuvee.Error
import cuvee.core._

// polymorphic functions are monomorphized before they are passed to a solver,
// traces.bpl contains the combinators of trace equation systems, which solvers do not support
// the examples of horn are for -chc only, their procedures with a body have no contracts
def solvable =
  Examples.find(os.sub / "boogie", "bpl").filterNot(file => file.last == "traces.bpl" || file.segments.contains("horn"))

// runs the examples with -verify against z3,
// the first line of each example states whether all goals are valid
object Verify extends TestSuite:
  // errors reported for each expected result
  val expected = Map(
    "// expected: valid" -> Nil,
    "// expected: invalid" -> List("goal does not hold")
  )

  val tests =
    Examples.tests(solvable): file =>
      val first = os.read.lines(file).head
      assert(expected.contains(first))

      Examples.errors("-verify", "-monomorph", "-z3", file.toString) ==> expected(first)

// runs the examples with -chc against z3, which checks the clauses for satisfiability:
// sat if all queries hold, unsat if one of them fails
object Horn extends TestSuite:
  // status reported for each expected result
  val expected = Map(
    "// expected: valid" -> Status.Sat,
    "// expected: invalid" -> Status.Unsat
  )

  // the other examples are not covered, since their procedures with a body have contracts
  val tests =
    Examples.tests(Examples.find(os.sub / "boogie" / "horn", "bpl")): file =>
      val first = os.read.lines(file).head
      assert(expected.contains(first))

      val (_, results) = cuvee.Cuvee.run("-chc", "-monomorph", "-z3", file.toString)
      results.collect { case error: Error => error.msg } ==> Nil
      Examples.status(results) ==> expected(first)

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
      val file = os.temp("var x: int;", suffix = ".bpl")
      val (_, results) = cuvee.Cuvee.run("-z3", file.toString)
      assert(results.contains(Ack.Unsupported))
