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
    Examples.tests(Examples.find(os.sub / "dafny" / "vcgen", "dfy").filter(Examples.supported)): file =>
      val first = os.read.lines(file).head
      assert(expected.contains(first))

      Examples.errors("-verify", "-z3", file.toString) ==> expected(first)

// hybrid programs, whose goals are generated without errors, not passed to a solver:
// differential cuts for each invariant in sequence, followed by differential weakening,
// and methods with assumption-commitment contracts composed in parallel
object VerifyHybrid extends TestSuite:
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
    test("examples"):
      for file <- Examples.find(os.sub / "hybrid", "dfy")
      do Examples.errors(List("-verify", "-simplify", "-print", "null") ++ Examples.options(file) :+ file.toString*) ==> Nil

    test("no history"):
      Examples.check("dfy", "method p() { } method m() { parallel { p(); } }", "-verify") ==>
        List("parallel composition requires a global variable history")

    test("weakening"):
      ode(Nil, Le.real(zero, x)) ==> "forall x₁: real :: 0.0 < y ==> 0.0 <= x₁"

    test("cut"):
      ode(List(Le.real(zero, x)), Le.real(zero, x)) ==>
        "0.0 <= x" +
          " && (forall x₁: real, x'₁: real :: 0.0 < y && x'₁ == y ==> (x₁ :: 0.0 <= x₁)')" +
          " && (forall x₂: real :: 0.0 < y && 0.0 <= x₂ ==> 0.0 <= x₂)"
