package cuvee.test
package simplify

import utest._

import cuvee.Config
import cuvee.core._
import cuvee.simplify.{Ctx, Rule, Rewrite}

// patterns with the combinators trace, map, and all, as in the examples of Trace Equation Systems,
// where the first dependency of the expressions is the counter ⌊J⌋ of the iterations, J == counter(0, 1, n),
// as in TEQ.loop
object RewriteTraces extends TestSuite:
  // a rule whose variables are the free variables of its left-hand side
  def rw(lhs: Expr, rhs: Expr, cond: Expr = True) =
    Rule(lhs.free.toList, lhs, rhs, cond)

  val int = Sort.int
  val ints = Sort.seq(int)
  val trace = Sort.trace(int)
  val array = Sort.array(int, int)

  val steps = Fun("steps", Nil, Fun.formals(ints), int)
  val sums = Fun("sums", Nil, Fun.formals(int, ints), trace)
  val selects = Fun("selects", Nil, Fun.formals(array, ints), ints)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  // variables of the rules
  val i = Var("i", int)
  val c = Var("c", int)
  val x = Var("x", int)
  val v = Var("v", int)
  val k = Var("k", int)
  val a = Var("a", array)
  val K = Var("K", trace)
  val V = Var("V", ints)
  val Ks = Var("Ks", ints)

  // variables of the expressions
  val s = Var("s", int)
  val j = Var("j", int)
  val arr = Var("arr", array)
  val J = Var("J", trace)
  val n = Var("n", int)

  // the counter of the iterations
  val ctx = Ctx.empty.assume(Eq(J, Counter(Zero.int, One.int, n)))

  def R(rules: List[Rule], expr: Expr, ctx: Ctx = ctx) =
    Rewrite.rewrite(Config.default, State.empty, ctx.withRules(rules), expr)

  // trace(i, for ⌊K⌋ do i, k ↦ i + c) = counter(i, c, steps(⌊K⌋))
  val counterRule =
    rw(Trace(i, List(Butlast(K)), x, List(k), List(Upd(True, Plus.int(x, c)))), Counter(i, c, app(steps, Butlast(K))))

  // trace(i, for V do x, v ↦ x + v) = sums(i, V)
  val sumsRule =
    rw(Trace(i, List(V), x, List(v), List(Upd(True, Plus.int(x, v)))), app(sums, i, V))

  // map(for K yield k ↦ a[k]) = selects(a, K)
  val selectsRule =
    rw(Maps(List(Ks), List(k), List(Upd(True, Select(a, k)))), app(selects, a, Ks))

  val tests = Tests:
    // example 2.3, the counter is matched modulo commutativity
    test("counter"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), List(Upd(True, Plus.int(One.int, s))))
      R(List(counterRule), expr) ==> Counter(Zero.int, One.int, app(steps, Butlast(J)))

    // example 2.6, the dependency V is instantiated by a map over the dependencies of the expression
    test("sums"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), List(Upd(True, Plus.int(s, Select(arr, j)))))
      val values = Maps(List(Butlast(J)), List(j), List(Upd(True, Select(arr, j))))
      R(List(sumsRule), expr) ==> app(sums, Zero.int, values)

    // ... which is then recognized as selects, example 6.2
    test("sums of selects"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), List(Upd(True, Plus.int(s, Select(arr, j)))))
      R(List(sumsRule, selectsRule), expr) ==> app(sums, Zero.int, app(selects, arr, Butlast(J)))

    // a bound variable that is the value directly yields the dependency itself
    test("dependency"):
      val W = Var("W", ints)
      val w = Var("w", int)
      val expr = Trace(Zero.int, List(Butlast(J), W), s, List(j, w), List(Upd(True, Plus.int(w, s))))
      R(List(sumsRule), expr) ==> app(sums, Zero.int, W)

    // the counter of the iterations is kept in the map in front, also if the value does not use it,
    // with its bound variable
    test("counters"):
      val W = Var("W", ints)
      val w = Var("w", int)
      val L = Var("L", trace)
      val l = Var("l", int)
      val ctx_ = ctx.assume(Eq(L, Counter(One.int, Plus.int(One.int, One.int), n)))
      val square = Times.int(w, w)

      val expr = Trace(Zero.int, List(Butlast(J), W), s, List(j, w), List(Upd(True, Plus.int(s, square))))
      R(List(sumsRule), expr) ==> app(sums, Zero.int, Maps(List(Butlast(J), W), List(j, w), List(Upd(True, square))))

      // other counters are dropped if they are not used
      val other = Trace(Zero.int, List(Butlast(L), W, Butlast(J)), s, List(l, w, j), List(Upd(True, Plus.int(s, square))))
      R(List(sumsRule), other, ctx_) ==>
        app(sums, Zero.int, Maps(List(Butlast(J), W), List(j, w), List(Upd(True, square))))

      // and kept behind the counter of the iterations if they are
      val used = Trace(Zero.int, List(Butlast(L), W, Butlast(J)), s, List(l, w, j), List(Upd(True, Plus.int(s, Times.int(l, w)))))
      R(List(sumsRule), used, ctx_) ==>
        app(sums, Zero.int, Maps(List(Butlast(J), Butlast(L), W), List(j, l, w), List(Upd(True, Times.int(l, w)))))

      // without a counter of the iterations, the first dependency of the expression comes first
      val none = Trace(Zero.int, List(W, Butlast(L)), s, List(w, l), List(Upd(True, Plus.int(s, Times.int(l, l)))))
      R(List(sumsRule), none, Ctx.empty.assume(Eq(L, Counter(One.int, Plus.int(One.int, One.int), n)))) ==>
        app(sums, Zero.int, Maps(List(W, Butlast(L)), List(w, l), List(Upd(True, Times.int(l, l)))))

    // the value must not depend on the accumulator
    test("accumulator"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), List(Upd(True, Plus.int(s, Times.int(s, j)))))
      R(List(sumsRule), expr) ==> expr

    // every case of the update of the expression is covered by the single case of the pattern
    test("cases"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), List(
        Upd(Lt.int(j, n), Plus.int(s, One.int)),
        Upd(Not(Lt.int(j, n)), Plus.int(s, One.int))
      ))
      R(List(counterRule), expr) ==> Counter(Zero.int, One.int, app(steps, Butlast(J)))

    // different increments in the cases are not a counter
    test("different cases"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), List(
        Upd(Lt.int(j, n), Plus.int(s, One.int)),
        Upd(Not(Lt.int(j, n)), Plus.int(s, Plus.int(One.int, One.int)))
      ))
      R(List(counterRule), expr) ==> expr

    // all(for ⌊K⌋ check k ↦ k < len) with the bound variable related to that of the expression
    test("all"):
      val len = Var("len", int)
      val rule = rw(Invs(List(Butlast(K)), List(k), Lt.int(k, len)), Le.int(app(steps, Butlast(K)), len))
      val expr = Invs(List(Butlast(J)), List(j), Lt.int(j, n))
      R(List(rule), expr) ==> Le.int(app(steps, Butlast(J)), n)

    // the variables of the rule must not capture the bound variables of the expression
    test("capture"):
      val rule = rw(Invs(List(Butlast(K)), List(k), Lt.int(c, k)), True)
      val expr = Invs(List(Butlast(J)), List(j), Lt.int(j, j))
      R(List(rule), expr) ==> expr
