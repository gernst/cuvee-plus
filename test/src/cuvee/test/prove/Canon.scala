package cuvee.test
package prove

import utest._

import cuvee.core._
import cuvee.prove.Canon

// the canonical forms of terms with binders of the engine of -prove: alpha-variants, the order of dependencies and
// of cases, idempotence
object CanonTests extends TestSuite:
  val n = Var("n", Sort.int)
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val k = Var("k", Sort.int)
  val j = Var("j", Sort.int)
  val xs = Var("xs", Sort.list(Sort.int))
  val ys = Var("ys", Sort.list(Sort.int))

  def lit(v: Int) = Lit(BigInt(v), Sort.int)
  val ks = Butlast(Counter(Ints.zero, Ints.one, n))

  val tests = Tests:
    // bound variables renamed, nothing else
    test("alpha"):
      val a = Invs(List(ks), List(k), Ints.lt(k, x))
      val b = Invs(List(ks), List(j), Ints.lt(j, x))
      assert(Canon.term(a) == Canon.term(b))
      assert(Canon.equal(a, b))
      assert(!Canon.equal(a, Invs(List(ks), List(j), Ints.lt(j, y))))
      assert(Canon.term(Canon.term(a)) == Canon.term(a))

    // the order of the dependencies does not matter, their bound variables follow them
    test("dependencies"):
      val a = Invs(List(ks, xs), List(k, x), Ints.lt(k, x))
      val b = Invs(List(xs, ks), List(y, j), Ints.lt(j, y))
      assert(Canon.equal(a, b))
      assert(!Canon.equal(a, Invs(List(xs, ks), List(y, j), Ints.lt(y, j))))

    // the order of the cases of a choice does not matter, and the free variables are kept
    test("cases"):
      val a = Trace(lit(0), List(ks), x, List(k), Eps(List(Upd(Ints.lt(k, y), Ints.plus(x, lit(1))), Upd(Ints.le(y, k), x))))
      val b = Trace(lit(0), List(ks), j, List(x), Eps(List(Upd(Ints.le(y, x), j), Upd(Ints.lt(x, y), Ints.plus(j, lit(1))))))
      assert(Canon.equal(a, b))
      assert(Canon.term(a).free == Set(n, y))

    // nested binders: sibling scopes reuse the names, nested scopes do not
    test("nested"):
      val a = All(List(x), And(List(Ex(List(y), Eq(x, y)), Ex(List(k), Eq(x, k)))))
      val b = All(List(k), And(List(Ex(List(x), Eq(k, x)), Ex(List(j), Eq(j, k)))))
      assert(Canon.equal(a, b))
      val c = All(List(x), Ex(List(y), Eq(x, y)))
      val d = All(List(x), Ex(List(y), Eq(y, y)))
      assert(!Canon.equal(c, d))

    // a closed side condition is known if a fact is an alpha-variant of it (see Rewrite.known), also through the
    // classes: n == m makes invs over ⌊counter(0, 1, m)⌋ known for the fact over ⌊counter(0, 1, n)⌋
    test("known"):
      val m = Var("m", Sort.int)
      val fact = Invs(List(ks), List(k), Ints.lt(k, x))
      val ctx = cuvee.prove.Context.empty(State.empty).assume(List(fact), Nil)
      assert(cuvee.prove.Rewrite.known(ctx, ctx.known, Invs(List(ks), List(j), Ints.lt(j, x))))
      assert(!cuvee.prove.Rewrite.known(ctx, ctx.known, Invs(List(ks), List(j), Ints.le(j, x))))
      val ctx_ = ctx.assume(List(Eq(n, m)), Nil)
      assert(cuvee.prove.Rewrite.known(ctx_, ctx_.known, Invs(List(Butlast(Counter(Ints.zero, Ints.one, m))), List(k), Ints.lt(k, x))))

    // terms without binders are compared as they are, which costs no traversal
    test("plain"):
      assert(!Canon.binds(Ints.plus(x, y)))
      assert(Canon.equal(Ints.plus(x, y), Ints.plus(x, y)))
      assert(!Canon.equal(Ints.plus(x, y), Ints.plus(y, x)))
