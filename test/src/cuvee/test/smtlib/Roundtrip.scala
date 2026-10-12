package cuvee.test
package smtlib

import utest._

// printing the SMT-LIB examples is stable when the output is parsed again
object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.printing(Examples.valid(os.sub / "smtlib", "smt2"))): file =>
      Examples.roundtrip(file, Nil)

// the programs of the Dafny and Boogie examples printed as SMT-LIB can be read back, and printing them again is stable;
// the sorts and datatypes of the preludes of the frontends are not printed (see TODO.md), hence only examples without
object Programs extends TestSuite:
  // function types are not read back, since lambdas of SMT-LIB are arrays;
  // likewise the datatypes Nat and List of teq.dfy (see -teq), and the combinators of the lemma database, whose
  // dependencies ⌊...⌋ refer to its declarations, e.g. selects(a, ⌊counter(0, 1, n)⌋)
  val prelude = List("tuple", "event", "chan", "seq<", "datatype", "type ", "->", "List<", ": Nat", "⌊")

  def plain(file: os.Path) =
    !prelude.exists(os.read(file).contains)

  val tests =
    Examples.tests(Examples.printing((Examples.valid(os.sub / "dafny", "dfy") ++ Examples.valid(os.sub / "boogie", "bpl")).filter(plain))): file =>
      Examples.roundtrip(file, List("-print", "smt2"))
