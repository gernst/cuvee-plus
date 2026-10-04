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

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val zero = Lit(BigInt(0), Sort.int)

  // the formula with fresh variables numbered from 1
  def ode(invs: List[Expr], post: Expr) =
    Var.reset()
    val phi = cuvee.verify.Verify.ode(List(x), List(y), Lt.int(zero, y), invs, post)
    cuvee.dafny.Printer.lines(phi).mkString(" ").replaceAll(" +", " ")

  val tests = Tests:
    // the derivatives are simplified away before the goals are passed to z3
    test("hybrid.dfy"):
      val hybrid = Examples.root / "hybrid.dfy"
      Examples.errors("-verify", "-simplify", "-z3", hybrid.toString) ==> Nil

    test("weakening"):
      ode(Nil, Le.int(zero, x)) ==> "forall x₁: int :: 0 < y ==> 0 <= x₁"

    test("cut"):
      ode(List(Le.int(zero, x)), Le.int(zero, x)) ==>
        "0 <= x" +
          " && (forall x₁: int, x'₁: int :: 0 < y && x'₁ == y ==> (x₁ :: 0 <= x₁)')" +
          " && (forall x₂: int :: 0 < y && 0 <= x₂ ==> 0 <= x₂)"
