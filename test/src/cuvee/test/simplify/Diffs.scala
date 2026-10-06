package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.Diffs

// difference constraints on Int, whose closure detects negative cycles, i.e., inconsistent facts
object DiffsTests extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val n = Var("n", Sort.int)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)

  def lit(k: Int) = Lit(BigInt(k), Sort.int)

  def facts(phis: Expr*) =
    phis.foldLeft(Diffs.empty)(_.assume(_))

  val tests = Tests:
    // the bounds of the loop counter in the goal of array_1-1
    test("bounds"):
      val ctx = facts(Le.int(Zero.int, n), Le.int(lit(1024), n))
      assert(!ctx.inconsistent)
      assert(ctx.assume(Lt.int(n, lit(1024))).inconsistent)
      assert(ctx.assume(Eq(n, Zero.int)).inconsistent)
      assert(!ctx.assume(Eq(n, lit(1024))).inconsistent)

    test("transitivity"):
      val ctx = facts(Le.int(x, y), Le.int(y, z))
      assert(!ctx.inconsistent)
      assert(ctx.deny(Le.int(x, z)).inconsistent)
      assert(ctx.assume(Not(Le.int(x, z))).inconsistent)
      assert(!ctx.deny(Le.int(z, x)).inconsistent)

    // strict comparisons are tightened on Int: x < y < x + 2 forces y == x + 1
    test("strict"):
      assert(facts(Lt.int(x, y), Lt.int(y, x)).inconsistent)
      assert(!facts(Le.int(x, y), Le.int(y, x)).inconsistent)
      val ctx = facts(Lt.int(x, y), Lt.int(y, Plus.int(x, lit(2))))
      assert(!ctx.inconsistent)
      assert(ctx.assume(Lt.int(Plus.int(x, One.int), y)).inconsistent)

    test("offsets"):
      assert(facts(Le.int(Plus.int(x, lit(3)), y), Le.int(y, Plus.int(x, lit(2)))).inconsistent)
      assert(!facts(Le.int(Plus.int(x, lit(3)), y), Le.int(y, Plus.int(x, lit(3)))).inconsistent)

    test("constants"):
      assert(facts(Le.int(One.int, Zero.int)).inconsistent)
      assert(!facts(Le.int(Zero.int, One.int)).inconsistent)

    // non-arithmetic terms and monomials with a factor are atoms
    test("atoms"):
      val fx = App(f, List(x))
      assert(facts(Le.int(fx, y), Lt.int(y, fx)).inconsistent)
      val twice = Times.int(lit(2), x)
      assert(facts(Le.int(twice, y), Lt.int(y, twice)).inconsistent)

    // facts that are no difference constraints are ignored, which is sound but incomplete
    test("ignored"):
      assert(facts(Le.int(Plus.int(x, y), Zero.int), Lt.int(Zero.int, Plus.int(x, y))) == Diffs.empty)
      assert(facts(Not(Eq(x, y)), Eq(x, y)).deny(Eq(x, y)) == facts(Eq(x, y)))

    // adding a fact leaves the collection it was added to unchanged
    test("immutable"):
      val ctx = facts(Le.int(x, y))
      val ctx_ = ctx.assume(Lt.int(y, x))
      assert(ctx_.inconsistent)
      assert(!ctx.inconsistent)
