package cuvee.test

import utest._

import cuvee.Config
import cuvee.core._
import cuvee.pipe.Verify

// -verify answers correct, incorrect, or unknown (see pipe.Verify, examples/*/verify)
object VerifyAnswers extends TestSuite:
  val tests = Tests:
    // a solver checks the output unless -verify is given, regardless of the order of the options
    test("options"):
      val check = Config.parse(Config.default, List("-z3", "-vcgen", "input.c"))
      assert(check.solver.nonEmpty, !check.verify)

      val verify = Config.parse(Config.default, List("-verify", "-vcgen", "-z3", "input.c"))
      assert(verify.solver.nonEmpty, verify.verify)

    // an obligation holds if the answer is the expected status, it is refuted by the opposite one unless it is
    // stronger than the specification
    test("outcome"):
      Verify.expected(Assert(Goal, Nil, True, Attrs.empty)) ==> Status.Unsat
      Verify.expected(CheckSat) ==> Status.Sat
      Verify.outcome(Status.Unsat, Status.Unsat, false) ==> Status.Correct
      Verify.outcome(Status.Unsat, Status.Sat, false) ==> Status.Incorrect
      Verify.outcome(Status.Unsat, Status.Sat, true) ==> Status.Unknown
      Verify.outcome(Status.Unsat, Status.Unknown, false) ==> Status.Unknown
      Verify.outcome(Status.Sat, Status.Sat, false) ==> Status.Correct
      Verify.outcome(Status.Sat, Status.Unsat, false) ==> Status.Incorrect

    test("aggregation"):
      Verify.and(Status.Correct, Status.Unknown) ==> Status.Unknown
      Verify.and(Status.Unknown, Status.Incorrect) ==> Status.Incorrect
      Verify.and(Status.Correct, Status.Correct) ==> Status.Correct
