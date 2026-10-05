package cuvee.test
package dafny

import utest._

// runs the examples with -verify against z3,
// the first line of each example states whether all goals are valid:
//   "// expected: valid" or "// expected: invalid"
object Verify extends TestSuite:
  // errors reported for each expected result
  val expected = Map(
    "// expected: valid" -> Nil,
    "// expected: invalid" -> List("goal does not hold")
  )

  val tests =
    Examples.tests(Examples.find(os.sub / "dafny" / "vcgen", "dfy")): file =>
      val first = os.read.lines(file).head
      assert(expected.contains(first))

      Examples.errors("-verify", "-z3", file.toString) ==> expected(first)

// differential cuts for each invariant in sequence, followed by differential weakening
object VerifyOde extends TestSuite:
  import cuvee.core._

  val x = Var("x", Sort.real)
  val y = Var("y", Sort.real)
  val zero = Zero.real

  // the formula with fresh variables numbered from 1
  def ode(invs: List[Expr], post: Expr) =
    Var.reset()
    val phi = cuvee.verify.Verify.ode(List(x), List(y), Lt.real(zero, y), invs, post)
    cuvee.dafny.Printer.lines(phi).mkString(" ").replaceAll(" +", " ")

  val tests = Tests:
    // the derivatives are simplified away before the goals are passed to z3
    test("hybrid.dfy"):
      val hybrid = Examples.root / "dafny" / "hybrid.dfy"
      Examples.errors("-verify", "-simplify", "-z3", hybrid.toString) ==> Nil

    test("weakening"):
      ode(Nil, Le.real(zero, x)) ==> "forall x₁: real :: 0.0 < y ==> 0.0 <= x₁"

    test("cut"):
      ode(List(Le.real(zero, x)), Le.real(zero, x)) ==>
        "0.0 <= x" +
          " && (forall x₁: real, x'₁: real :: 0.0 < y && x'₁ == y ==> (x₁ :: 0.0 <= x₁)')" +
          " && (forall x₂: real :: 0.0 < y && 0.0 <= x₂ ==> 0.0 <= x₂)"

// sequences, whose updates are supported by cvc5 only
object VerifySeq extends TestSuite:
  val tests = Tests:
    test("seq.dfy"):
      val seq = Examples.root / "dafny" / "seq.dfy"
      Examples.errors("-verify", "-cvc5", seq.toString) ==> Nil

// finite sets and multisets, which are supported by cvc5 only
object VerifySets extends TestSuite:
  val tests = Tests:
    test("sets.dfy"):
      Examples.errors("-verify", "-cvc5", (Examples.root / "dafny" / "sets.dfy").toString) ==> Nil

    test("invalid_sets.dfy"):
      Examples.errors("-verify", "-cvc5", (Examples.root / "dafny" / "invalid_sets.dfy").toString) ==> List("goal does not hold")

// methods with assumption-commitment contracts composed in parallel
object VerifyPar extends TestSuite:
  val tests = Tests:
    test("par.dfy"):
      val par = Examples.root / "dafny" / "par.dfy"
      Examples.errors("-hybrid", "-verify", "-z3", par.toString) ==> Nil

    // the commitment of the other method does not imply the assumption
    test("assumption"):
      val par = os.read(Examples.root / "dafny" / "par.dfy").replace(
        "  requires c != d\n  assumes positive(history, c)\n  commits positive(history, c)",
        "  requires c != d\n  assumes positive(history, c)"
      )
      val file = os.temp(par, suffix = ".dfy")
      Examples.errors("-hybrid", "-verify", "-z3", file.toString) ==> List("goal does not hold")

    // the parallel composition extends the history, after which the commitment of main must hold
    test("commitment"):
      val par = os.read(Examples.root / "dafny" / "par.dfy")
      val good = par.replace("  ensures positive(history, c)\n{\n  parallel", "  ensures positive(history, c)\n  commits positive(history, c)\n{\n  parallel")
      val bad = par.replace("  ensures positive(history, c)\n{\n  parallel", "  ensures positive(history, c)\n  commits history == []\n{\n  parallel")
      assert(good != par && bad != par)
      Examples.errors("-hybrid", "-verify", "-z3", os.temp(good, suffix = ".dfy").toString) ==> Nil
      Examples.errors("-hybrid", "-verify", "-z3", os.temp(bad, suffix = ".dfy").toString) ==> List("goal does not hold")

    test("no history"):
      val file = os.temp("method p() { } method m() { parallel { p(); } }", suffix = ".dfy")
      Examples.errors("-verify", "-print", "null", file.toString) ==>
        List("parallel composition requires a global variable history")
