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
      val ctx = facts(Ints.le(Ints.zero, n), Ints.le(lit(1024), n))
      assert(!ctx.inconsistent)
      assert(ctx.assume(Ints.lt(n, lit(1024))).inconsistent)
      assert(ctx.assume(Eq(n, Ints.zero)).inconsistent)
      assert(!ctx.assume(Eq(n, lit(1024))).inconsistent)

    test("transitivity"):
      val ctx = facts(Ints.le(x, y), Ints.le(y, z))
      assert(!ctx.inconsistent)
      assert(ctx.deny(Ints.le(x, z)).inconsistent)
      assert(ctx.assume(Not(Ints.le(x, z))).inconsistent)
      assert(!ctx.deny(Ints.le(z, x)).inconsistent)

    // strict comparisons are tightened on Int: x < y < x + 2 forces y == x + 1
    test("strict"):
      assert(facts(Ints.lt(x, y), Ints.lt(y, x)).inconsistent)
      assert(!facts(Ints.le(x, y), Ints.le(y, x)).inconsistent)
      val ctx = facts(Ints.lt(x, y), Ints.lt(y, Ints.plus(x, lit(2))))
      assert(!ctx.inconsistent)
      assert(ctx.assume(Ints.lt(Ints.plus(x, Ints.one), y)).inconsistent)

    test("offsets"):
      assert(facts(Ints.le(Ints.plus(x, lit(3)), y), Ints.le(y, Ints.plus(x, lit(2)))).inconsistent)
      assert(!facts(Ints.le(Ints.plus(x, lit(3)), y), Ints.le(y, Ints.plus(x, lit(3)))).inconsistent)

    test("constants"):
      assert(facts(Ints.le(Ints.one, Ints.zero)).inconsistent)
      assert(!facts(Ints.le(Ints.zero, Ints.one)).inconsistent)

    // non-arithmetic terms and monomials with a factor are atoms
    test("atoms"):
      val fx = App(f, List(x))
      assert(facts(Ints.le(fx, y), Ints.lt(y, fx)).inconsistent)
      val twice = Ints.times(lit(2), x)
      assert(facts(Ints.le(twice, y), Ints.lt(y, twice)).inconsistent)

    // facts that are no difference constraints are ignored, which is sound but incomplete
    test("ignored"):
      assert(facts(Ints.le(Ints.plus(x, y), Ints.zero), Ints.lt(Ints.zero, Ints.plus(x, y))) == Diffs.empty)
      assert(facts(Not(Eq(x, y)), Eq(x, y)).deny(Eq(x, y)) == facts(Eq(x, y)))

    // adding a fact leaves the collection it was added to unchanged
    test("immutable"):
      val ctx = facts(Ints.le(x, y))
      val ctx_ = ctx.assume(Ints.lt(y, x))
      assert(ctx_.inconsistent)
      assert(!ctx.inconsistent)
