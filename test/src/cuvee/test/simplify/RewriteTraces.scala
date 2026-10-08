package cuvee.test
package simplify

import utest._

import cuvee.Config
import cuvee.core._
import cuvee.simplify.{Context, Rule, Rewrite}

// patterns with the combinators trace, map, and all, as in the examples of Trace Equation Systems,
// where the first dependency of the expressions is the counter ⌊J⌋ of the iterations, J == counter(0, 1, n),
// as in TEQ.loop
object RewriteTraces extends TestSuite:
  // a rule whose type parameters and variables are the free ones of its left-hand side
  def rw(lhs: Expr, rhs: Expr, cond: Expr = True) =
    Rule(lhs.params, lhs.free, lhs, rhs, cond)

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
  val ctx = Context.empty.assume(Eq(J, Counter(Zero.int, One.int, n)))

  def R(rules: List[Rule], expr: Expr, ctx: Context = ctx) =
    Rewrite.rewrite(Config.default, State.empty, ctx.withRules(rules), expr)

  // trace(i, for ⌊K⌋ do i, k ↦ i + c) = counter(i, c, steps(⌊K⌋))
  val counterRule =
    rw(Trace(i, List(Butlast(K)), x, List(k), Plus.int(x, c)), Counter(i, c, app(steps, Butlast(K))))

  // trace(i, for V do x, v ↦ x + v) = sums(i, V)
  val sumsRule =
    rw(Trace(i, List(V), x, List(v), Plus.int(x, v)), app(sums, i, V))

  // map(for K yield k ↦ a[k]) = selects(a, K)
  val selectsRule =
    rw(Maps(List(Ks), List(k), Select(a, k)), app(selects, a, Ks))

  val tests = Tests:
    // example 2.3, the counter is matched modulo commutativity
    test("counter"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), Plus.int(One.int, s))
      R(List(counterRule), expr) ==> Counter(Zero.int, One.int, app(steps, Butlast(J)))

    // example 2.6, the dependency V is instantiated by a map over the dependencies of the expression
    test("sums"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), Plus.int(s, Select(arr, j)))
      val values = Maps(List(Butlast(J)), List(j), Select(arr, j))
      R(List(sumsRule), expr) ==> app(sums, Zero.int, values)

    // a bound variable that is the value directly yields the dependency itself
    test("dependency"):
      val W = Var("W", ints)
      val w = Var("w", int)
      val expr = Trace(Zero.int, List(Butlast(J), W), s, List(j, w), Plus.int(w, s))
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

      val expr = Trace(Zero.int, List(Butlast(J), W), s, List(j, w), Plus.int(s, square))
      R(List(sumsRule), expr) ==> app(sums, Zero.int, Maps(List(Butlast(J), W), List(j, w), square))

      // other counters are dropped if they are not used
      val other = Trace(Zero.int, List(Butlast(L), W, Butlast(J)), s, List(l, w, j), Plus.int(s, square))
      R(List(sumsRule), other, ctx_) ==>
        app(sums, Zero.int, Maps(List(Butlast(J), W), List(j, w), square))

      // and kept behind the counter of the iterations if they are
      val used = Trace(Zero.int, List(Butlast(L), W, Butlast(J)), s, List(l, w, j), Plus.int(s, Times.int(l, w)))
      R(List(sumsRule), used, ctx_) ==>
        app(sums, Zero.int, Maps(List(Butlast(J), Butlast(L), W), List(j, l, w), Times.int(l, w)))

      // without a counter of the iterations, the first dependency of the expression comes first
      val none = Trace(Zero.int, List(W, Butlast(L)), s, List(w, l), Plus.int(s, Times.int(l, l)))
      R(List(sumsRule), none, Context.empty.assume(Eq(L, Counter(One.int, Plus.int(One.int, One.int), n)))) ==>
        app(sums, Zero.int, Maps(List(W, Butlast(L)), List(w, l), Times.int(l, l)))

    // the value must not depend on the accumulator
    test("accumulator"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), Plus.int(s, Times.int(s, j)))
      R(List(sumsRule), expr) ==> expr

    // every case of the update of the expression is covered by the single case of the pattern
    test("cases"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), Eps(List(
        Upd(Lt.int(j, n), Plus.int(s, One.int)),
        Upd(Not(Lt.int(j, n)), Plus.int(s, One.int))
      )))
      R(List(counterRule), expr) ==> Counter(Zero.int, One.int, app(steps, Butlast(J)))

    // different increments in the cases are not a counter
    test("different cases"):
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), Eps(List(
        Upd(Lt.int(j, n), Plus.int(s, One.int)),
        Upd(Not(Lt.int(j, n)), Plus.int(s, Plus.int(One.int, One.int)))
      )))
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

    // higher-order patterns P(x) of variables of function type applied to bound variables (Miller's fragment),
    // where the dependency Xs follows from the bound variable of the expression that x corresponds to
    test("higher-order"):
      val Xs = Var("Xs", ints)
      val P = Var("P", Arrow(List(int), Sort.bool))
      val Q = Var("Q", Arrow(List(int), Sort.bool))
      val rule = rw(
        Invs(List(Xs), List(x), And(Apply(P, List(x)), Apply(Q, List(x)))),
        And(Invs(List(Xs), List(x), Apply(P, List(x))), Invs(List(Xs), List(x), Apply(Q, List(x))))
      )

      val expr = Invs(List(Butlast(J)), List(j), And(Lt.int(j, n), Le.int(Zero.int, j)))
      val p = Lam(List(j), Lt.int(j, n), Arrow(List(int), Sort.bool))
      val q = Lam(List(j), Le.int(Zero.int, j), Arrow(List(int), Sort.bool))
      R(List(rule), expr) ==>
        And(Invs(List(Butlast(J)), List(x), Apply(p, List(x))), Invs(List(Butlast(J)), List(x), Apply(q, List(x))))

      // the simplifier beta-reduces the instantiated right-hand side, here without the counter,
      // whose bounds would decide both
      val phi = cuvee.simplify.Simplify.simplify(Config.default, State.empty, Context.pos.withRules(List(rule)), expr)
      phi ==> And(Invs(List(Butlast(J)), List(j), Lt.int(j, n)), Invs(List(Butlast(J)), List(j), Le.int(Zero.int, j)))

      // a single bound variable of the pattern cannot abstract two of the expression
      val W = Var("W", ints)
      val w = Var("w", int)
      val two = Invs(List(Butlast(J), W), List(j, w), And(Lt.int(j, n), Lt.int(w, j)))
      R(List(rule), two) ==> two

    // repeated occurrences of a higher-order variable must agree
    test("higher-order repeated"):
      val Xs = Var("Xs", ints)
      val P = Var("P", Arrow(List(int), Sort.bool))
      val rule = rw(Invs(List(Xs), List(x), And(Apply(P, List(x)), Not(Apply(P, List(x))))), False)

      R(List(rule), Invs(List(Butlast(J)), List(j), And(Lt.int(j, n), Not(Lt.int(j, n))))) ==> False
      val other = Invs(List(Butlast(J)), List(j), And(Lt.int(j, n), Not(Lt.int(j, s))))
      R(List(rule), other) ==> other

    // the accumulator may be abstracted as well, unlike by first-order variables of the rule
    test("higher-order accumulator"):
      val Xs = Var("Xs", ints)
      val F = Var("F", Arrow(List(int, int), int))
      val fold = Fun("fold", Nil, Fun.formals(int, ints, Arrow(List(int, int), int)), trace)
      val rule = rw(Trace(i, List(Xs), x, List(v), Apply(F, List(x, v))), app(fold, i, Xs, F))

      val update = Plus.int(Times.int(s, j), One.int)
      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), update)
      R(List(rule), expr) ==> app(fold, Zero.int, Butlast(J), Lam(List(s, j), update, Arrow(List(int, int), int)))

    // a guard D(x, v) && φ of the pattern binds D to the whole guard of the expression, from which φ must follow
    test("higher-order guards"):
      val Xs = Var("Xs", ints)
      val D = Var("D", Arrow(List(int, int), Sort.bool))
      val F = Var("F", Arrow(List(int, int), int))
      val incs = Fun("incs", Nil, Fun.formals(int, ints, Arrow(List(int, int), Sort.bool), Arrow(List(int, int), int)), trace)
      val rule = rw(
        Trace(i, List(Xs), x, List(v), Eps(List(Upd(And(Apply(D, List(x, v)), Lt.int(x, Apply(F, List(x, v)))), Apply(F, List(x, v)))))),
        app(incs, i, Xs, D, F)
      )

      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), Eps(List(Upd(Lt.int(Zero.int, j), Plus.int(s, j)))))
      val App(fun, _, _, List(_, _, d, f)) = R(List(rule), expr): @unchecked
      fun ==> incs
      d ==> Lam(List(s, j), Lt.int(Zero.int, j), Arrow(List(int, int), Sort.bool))
      f ==> Lam(List(s, j), Plus.int(s, j), Arrow(List(int, int), int))

      // the increase does not follow from the guard, here with the bounds 0 <= j < n of the counter of the iterations,
      // whereas a guard j < 0 contradicts them, such that the case is unreachable and any increase follows
      val other = Trace(Zero.int, List(Butlast(J)), s, List(j), Eps(List(Upd(Lt.int(j, n), Plus.int(s, j)))))
      R(List(rule), other) ==> other

    // the conjuncts of a guard that does not match the guard of the expression as a whole follow from it,
    // or are matched against its conjuncts, which instantiates variables that occur only in the guard, here b = n
    test("guard conjuncts"):
      val Xs = Var("Xs", ints)
      val b = Var("b", int)
      val capped = Fun("capped", Nil, Fun.formals(int, ints, int), trace)
      val rule = rw(
        Trace(i, List(Xs), x, List(v), Eps(List(Upd(And(Lt.int(Zero.int, v), Le.int(x, b)), Plus.int(x, v))))),
        app(capped, i, Xs, b)
      )

      val expr = Trace(Zero.int, List(Butlast(J)), s, List(j), Eps(List(Upd(And(Le.int(s, n), Lt.int(Zero.int, j)), Plus.int(s, j)))))
      R(List(rule), expr) ==> app(capped, Zero.int, Butlast(J), n)

      // the bound must be among the conjuncts of the guard of the expression
      val other = Trace(Zero.int, List(Butlast(J)), s, List(j), Eps(List(Upd(Lt.int(Zero.int, j), Plus.int(s, j)))))
      R(List(rule), other) ==> other
