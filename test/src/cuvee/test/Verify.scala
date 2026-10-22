package cuvee.test

import utest._

import cuvee.core._
import cuvee.pipe.Sink
import cuvee.verify.Horn

// the goals and lemmas are answered correct, incorrect, or unknown by the sink (see Sink.passive, Solver.sink,
// examples/*/verify)
object VerifyAnswers extends TestSuite:
  val tests = Tests:
    // without solver, goals are decided by their form, a refutation of a goal that is stronger than the
    // specification is no counterexample
    test("passive"):
      Sink.passive(Assert(Goal, Nil, True, Attrs.empty)) ==> Status.Correct
      Sink.passive(Assert(Goal, Nil, False, Attrs.empty)) ==> Status.Incorrect
      Sink.passive(Assert(Goal, Nil, False, Attrs.from("abstract"))) ==> Status.Unknown
      Sink.passive(Assert(Goal, Nil, Var("x", Sort.bool), Attrs.empty)) ==> Status.Unknown
      Sink.passive(Assert(Lemma, Nil, False, Attrs.from("free"))) ==> Ack.Success

    // the clauses of Horn are satisfiable iff the program is correct
    test("horn"):
      Horn.checked(Status.Sat) ==> Status.Correct
      Horn.checked(Status.Unsat) ==> Status.Incorrect
      Horn.checked(Status.Unknown) ==> Status.Unknown
