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
    Examples.tests(Examples.find(os.sub / "vcgen", "dfy")): file =>
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
      val hybrid = Examples.root / "hybrid.dfy"
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
      val seq = Examples.root / "seq.dfy"
      Examples.errors("-verify", "-cvc5", seq.toString) ==> Nil

// methods with assumption-commitment contracts composed in parallel
object VerifyPar extends TestSuite:
  val tests = Tests:
    test("par.dfy"):
      val par = Examples.root / "par.dfy"
      Examples.errors("-verify", "-z3", par.toString) ==> Nil

    // the commitment of the other method does not imply the assumption
    test("assumption"):
      val par = os.read(Examples.root / "par.dfy").replace(
        "  requires c != d\n  assumes positive(history, c)\n  commits positive(history, c)",
        "  requires c != d\n  assumes positive(history, c)"
      )
      val file = os.temp(par, suffix = ".dfy")
      Examples.errors("-verify", "-z3", file.toString) ==> List("goal does not hold")
