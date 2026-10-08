package cuvee.test
package dafny

import utest._

// the examples in dafny/language, dafny/teq, dafny/horn, dafny/sorts, dafny/parsing, and dafny/printing,
// each with its command line in the first line, e.g. ./Cuvee.sh -print null ... for the errors of a program
object Parsing extends TestSuite:
  val dirs = List("language", "teq", "horn", "sorts", "parsing", "printing")

  val tests =
    Examples.checked(dirs.flatMap(dir => Examples.find(os.sub / "dafny" / dir, "dfy") ++ Examples.find(os.sub / "dafny" / dir, "smt2")))
