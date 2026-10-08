package cuvee.test
package boogie

import utest._

// printing the Boogie examples is stable when the output is parsed again, the original file is not compared;
// the cases of the printer are in examples/boogie/printing and examples/smtlib/printing/boogie*.smt2
object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.valid(os.sub / "boogie", "bpl")): file =>
      Examples.roundtrip(file, Nil)
