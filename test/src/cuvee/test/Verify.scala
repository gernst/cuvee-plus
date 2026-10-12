package cuvee.test

import utest._

import cuvee.Config
import cuvee.Error
import cuvee.core._
import cuvee.pipe.Verify

// -verify answers correct, incorrect, or unknown (see pipe.Verify, examples/*/verify); the combinations of options
// that the final configuration rejects are raised before the pipeline runs, hence they are no examples
object VerifyAnswers extends TestSuite:
  def rejected(args: String*): String =
    try
      Config.parse(Config.default, args.toList :+ "input.c")
      "accepted"
    catch case error: Error => error.msg

  val tests = Tests:
    test("options"):
      rejected("-verify", "-z3") ==> "-verify needs -vcgen, -teq, or -chc"
      rejected("-vcgen", "-verify", "-print", "dfy") ==> "-verify has no output for -print or -o"
      rejected("-vcgen", "-check") ==> "-check needs a solver (-z3 or -cvc5)"
      rejected("-vcgen", "-z3", "-check", "-verify") ==> "-check and -verify exclude each other"

      // a solver checks the output by default, regardless of the order of the options
      val config = Config.parse(Config.default, List("-z3", "-vcgen", "input.c"))
      assert(config.solver.nonEmpty, !config.check, !config.verify)

    // an obligation holds if the answer is the expected status, it is refuted by the opposite one unless it is
    // stronger than the specification
    test("outcome"):
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
