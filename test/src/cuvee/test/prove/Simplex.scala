package cuvee.test
package prove

import utest._

import cuvee.core._
import cuvee.prove.Classes
import cuvee.prove.Linear

// the linear constraints of the engine of -prove, decided by the simplex over the rationals, with the integers
// tightened: the tests of the difference constraints of the simplifier (test/simplify/Diffs.scala) and constraints
// with several atoms, which difference constraints cannot express
object SimplexTests extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val n = Var("n", Sort.int)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)

  def lit(k: Int) = Lit(BigInt(k), Sort.int)

  def facts(phis: Expr*) =
    phis.foldLeft(Linear.empty)(_.assume(_))

  val tests = Tests:
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

    // non-arithmetic terms and products are atoms
    test("atoms"):
      val fx = App(f, List(x))
      assert(facts(Ints.le(fx, y), Ints.lt(y, fx)).inconsistent)
      val twice = Ints.times(x, x)
      assert(facts(Ints.le(twice, y), Ints.lt(y, twice)).inconsistent)

    // several atoms per constraint, which no difference constraint expresses: x + y <= 10, x >= 6, y >= 5
    test("sums"):
      val ctx = facts(Ints.le(Ints.plus(x, y), lit(10)), Ints.le(lit(6), x))
      assert(!ctx.inconsistent)
      assert(ctx.assume(Ints.le(lit(5), y)).inconsistent)
      assert(!ctx.assume(Ints.le(lit(4), y)).inconsistent)

    // coefficients: 2 * x + 3 * y <= 12 with x, y >= 0 bounds y by 4 and x by 6
    test("coefficients"):
      val ctx = facts(Ints.le(Ints.plus(Ints.times(lit(2), x), Ints.times(lit(3), y)), lit(12)), Ints.le(Ints.zero, x), Ints.le(Ints.zero, y))
      assert(!ctx.inconsistent)
      assert(ctx.assume(Ints.lt(lit(4), y)).inconsistent)
      assert(ctx.assume(Ints.lt(lit(6), x)).inconsistent)
      assert(!ctx.assume(Eq(y, lit(4))).inconsistent)

    // on Int, 2 * x < 7 is x <= 3 by rounding, and 2 * x == 7 is inconsistent
    test("integers"):
      assert(facts(Ints.lt(Ints.times(lit(2), x), lit(7)), Ints.le(lit(4), x)).inconsistent)
      assert(!facts(Ints.lt(Ints.times(lit(2), x), lit(7)), Ints.le(lit(3), x)).inconsistent)
      assert(facts(Eq(Ints.times(lit(2), x), lit(7))).inconsistent)

    // a disequation contradicts constraints that determine the value
    test("disequations"):
      val ctx = facts(Ints.le(x, y), Ints.le(y, x))
      assert(ctx.deny(Eq(x, y)).inconsistent)
      assert(!facts(Ints.le(x, y)).deny(Eq(x, y)).inconsistent)

    // solutions of linear equations for a variable, e.g. x by 40 - n, which the classes keep and the simplifier
    // inlines, for the variable of the last rank (see Classes.rank), here x, bound inside of n
    test("solved"):
      val ctx = facts(Eq(Ints.plus(n, x), lit(40)))
      assert(ctx.assume(Ints.lt(lit(40), Ints.plus(n, x))).inconsistent)
      val classes = Classes.empty(Set()).assume(Eq(Ints.plus(n, x), lit(40)))(using Classes.Order(Classes.rank(y => if y == x then (2, 0) else (1, 0))))
      classes.solved.keySet ==> Set(x)
      assert(classes.equal(x, classes.solved(x)))

    // t div k for a positive literal k is bounded by k * (t div k) <= t <= k * (t div k) + k - 1: the midpoint of the
    // binary search lies in the interval, l <= (h + l) / 2 < h for l < h, and 0 <= (h + l) / 2 for 0 <= l
    test("division"):
      val mid = Ints.div(Ints.plus(y, x), lit(2))
      val ctx = facts(Ints.lt(x, y))
      assert(ctx.deny(Ints.le(x, mid)).inconsistent)
      assert(ctx.deny(Ints.lt(mid, y)).inconsistent)
      assert(!ctx.deny(Ints.lt(x, mid)).inconsistent)
      assert(ctx.assume(Ints.le(Ints.zero, x)).deny(Ints.le(Ints.zero, mid)).inconsistent)
      assert(!facts(Ints.le(x, y)).deny(Ints.lt(mid, y)).inconsistent)
