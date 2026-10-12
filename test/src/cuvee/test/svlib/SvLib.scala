package cuvee.test
package svlib

import utest._

import cuvee.core._
import cuvee.Cuvee

// printing the SV-LIB examples is stable after a round of parsing and printing, which asserts location invariants
// before their statements and moves the local variables of the body into the signature
object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.valid(os.sub / "svlib", "svlib")): file =>
      Examples.roundtrip(file, Nil, rounds = 1)

// the examples with -chc whose second line states whether the properties hold
object Horn extends TestSuite:
  def stated(file: os.Path) =
    os.read.lines(file)(1).startsWith("; expected:")

  val tests =
    Examples.tests(Examples.find(os.sub / "svlib", "svlib").filter(stated)): file =>
      Examples.show(List("-chc", "-z3", file.toString))
      val (_, results) = Cuvee.run("-chc", "-z3", file.toString)
      Examples.status(results) ==> (if Examples.holds(file) then Status.Sat else Status.Unsat)

// the annotations of annotate-tag commands are attached to the procedures and loops by the transforms,
// after the command, which may follow the procedure, and the properties of the output of -vcgen in SV-LIB parse again
object Annotations extends TestSuite:
  val file = Examples.root / "svlib" / "vcgen" / "loop_add.svlib"

  val tests = Tests:
    test("linked"):
      val cmds = Examples.input("-print", "null", file.toString)
      val tags = cmds.collect { case AnnotateTag(tag, _) => tag.indexed }
      tags ==> List("proc-add", "while-loop")
      // the contract is linked, the invariant is inline, neither is in the other place
      val List(proc) = cmds.collect { case DefineProc(_, _, attrs) => attrs }: @unchecked
      proc.requires ==> True
      proc.tags.map(_.indexed) ==> List("proc-add")

    test("verified"):
      val (cmds, errors) = Examples.output("-vcgen", "-print", "null", file.toString)
      errors ==> Nil
      // the goal of the procedure, the verify-call has none, as it assumes the precondition, the annotations are consumed
      cmds.collect { case Assert(Goal, _, _, _) => () }.length ==> 1
      cmds.collect { case AnnotateTag(_, _) => () } ==> Nil
      cmds.collect { case VerifyCall(proc, _) => proc.indexed } ==> List("add")
