package cuvee.test

import scala.io.Source

import util.Main
import cuvee.Cuvee
import cuvee.Error

// runs the examples with -verify against z3,
// the first line of each example states whether all goals are valid:
//   "// expected: valid" or "// expected: invalid"
object Verify extends Main with Tests:
  def main(args: Array[String]) =
    tests("verify examples"):
      val files = Tests.find("./examples/vcgen", ".dfy")

      for file <- files
      do
        test(file):
          val (cmds, results) = Cuvee.run("-verify", "-z3", file)
          val errors = results.collect { case error: Error => error.msg }

          expected(file) match
            case "valid" =>
              Check.equal("errors", errors, Nil)

            case "invalid" =>
              Check.equal("errors", errors, List("goal does not hold"))

  def expected(file: String) =
    val source = Source.fromFile(file)
    val first = try source.getLines().next() finally source.close()

    first.split("\\s+").toList match
      case List("//", "expected:", result) =>
        result

      case _ =>
        Error.raise("missing expected result", file, first)
