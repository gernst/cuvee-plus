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
    // the goals are generated and simplified without errors, not passed to a solver
    test("hybrid.dfy"):
      val hybrid = Examples.root / "dafny" / "hybrid.dfy"
      Examples.errors("-verify", "-simplify", "-print", "null", hybrid.toString) ==> Nil

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

// methods with assumption-commitment contracts composed in parallel,
// the goals are generated without errors, not passed to a solver
object VerifyPar extends TestSuite:
  val tests = Tests:
    test("par.dfy"):
      val par = Examples.root / "dafny" / "par.dfy"
      Examples.errors("-hybrid", "-verify", "-print", "null", par.toString) ==> Nil

    test("no history"):
      val file = os.temp("method p() { } method m() { parallel { p(); } }", suffix = ".dfy")
      Examples.errors("-verify", "-print", "null", file.toString) ==>
        List("parallel composition requires a global variable history")
