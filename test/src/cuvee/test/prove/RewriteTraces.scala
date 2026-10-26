package cuvee.test
package prove

import utest._

import cuvee.Config
import cuvee.core._
import cuvee.prove.Context
import cuvee.prove.Rule
import cuvee.prove.Rewrite

// patterns with the combinators trace, map, and all, as in the examples of Trace Equation Systems, in single steps
// whose results the simplifier would change (see examples/dafny/prove/traces*.dfy for the others),
// where the first dependency of the expressions is the counter ⌊J⌋ of the iterations, J == counter(0, 1, n),
// as in TEQ.loop
object RewriteTraces extends TestSuite:
  // a rule whose type parameters and variables are the free ones of its left-hand side
  def rw(lhs: Expr, rhs: Expr, cond: Expr = True) =
    Rule(lhs.params, lhs.free, lhs, rhs, cond)

  val int = Sort.int
  val ints = Sort.list(int)
  val trace = Sort.trace(int)

  val sums = Fun("sums", Nil, Fun.formals(int, ints), trace)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  // variables of the rules
  val i = Var("i", int)
  val x = Var("x", int)
  val v = Var("v", int)
  val k = Var("k", int)
  val K = Var("K", trace)
  val V = Var("V", ints)

  // variables of the expressions
  val s = Var("s", int)
  val j = Var("j", int)
  val J = Var("J", trace)
  val n = Var("n", Sort.int)

  // the counter of the iterations
  val ctx = Context.empty(State.empty).assume(Eq(J, Counter(Ints.zero, Ints.one, n)))

  def R(rules: List[Rule], expr: Expr, ctx: Context = ctx) =
    Rewrite.rewrite(Config.default, State.empty, ctx.withRules(rules), expr)

  // trace(i, for V do x, v ↦ x + v) = sums(i, V)
  val sumsRule =
    rw(Trace(i, List(V), x, List(v), Ints.plus(x, v)), app(sums, i, V))


  val tests = Tests:
    // the counter of the iterations is kept in the map in front, also if the value does not use it,
    // with its bound variable
    test("counters"):
      val W = Var("W", ints)
      val w = Var("w", int)
      val L = Var("L", trace)
      val l = Var("l", int)
      val ctx_ = ctx.assume(Eq(L, Counter(Ints.one, Ints.plus(Ints.one, Ints.one), n)))
      val square = Ints.times(w, w)

      val expr = Trace(Ints.zero, List(Butlast(J), W), s, List(j, w), Ints.plus(s, square))
      R(List(sumsRule), expr) ==> app(sums, Ints.zero, Maps(List(Butlast(J), W), List(j, w), square))

      // other counters are dropped if they are not used
      val other = Trace(Ints.zero, List(Butlast(L), W, Butlast(J)), s, List(l, w, j), Ints.plus(s, square))
      R(List(sumsRule), other, ctx_) ==>
        app(sums, Ints.zero, Maps(List(Butlast(J), W), List(j, w), square))

      // and kept behind the counter of the iterations if they are
      val used = Trace(Ints.zero, List(Butlast(L), W, Butlast(J)), s, List(l, w, j), Ints.plus(s, Ints.times(l, w)))
      R(List(sumsRule), used, ctx_) ==>
        app(sums, Ints.zero, Maps(List(Butlast(J), Butlast(L), W), List(j, l, w), Ints.times(l, w)))

      // without a counter of the iterations, the first dependency of the expression comes first
      val none = Trace(Ints.zero, List(W, Butlast(L)), s, List(w, l), Ints.plus(s, Ints.times(l, l)))
      R(List(sumsRule), none, Context.empty(State.empty).assume(Eq(L, Counter(Ints.one, Ints.plus(Ints.one, Ints.one), n)))) ==>
        app(sums, Ints.zero, Maps(List(W, Butlast(L)), List(w, l), Ints.times(l, l)))

    // a guard D(x, v) && φ of the pattern binds D to the whole guard of the expression, from which φ must follow
    test("higher-order guards"):
      val Xs = Var("Xs", ints)
      val D = Var("D", Arrow(List(int, int), Sort.bool))
      val F = Var("F", Arrow(List(int, int), int))
      val incs = Fun("incs", Nil, Fun.formals(int, ints, Arrow(List(int, int), Sort.bool), Arrow(List(int, int), int)), trace)
      val rule = rw(
        Trace(i, List(Xs), x, List(v), Eps(List(Upd(And(Apply(D, List(x, v)), Ints.lt(x, Apply(F, List(x, v)))), Apply(F, List(x, v)))))),
        app(incs, i, Xs, D, F)
      )

      val expr = Trace(Ints.zero, List(Butlast(J)), s, List(j), Eps(List(Upd(Ints.lt(Ints.zero, j), Ints.plus(s, j)))))
      val App(fun, _, _, List(_, _, d, f)) = R(List(rule), expr): @unchecked
      fun ==> incs
      d ==> Lam(List(s, j), Ints.lt(Ints.zero, j), Arrow(List(int, int), Sort.bool))
      f ==> Lam(List(s, j), Ints.plus(s, j), Arrow(List(int, int), int))

      // the increase does not follow from the guard, here with the bounds 0 <= j < n of the counter of the iterations,
      // whereas a guard j < 0 contradicts them, such that the case is unreachable and any increase follows
      val other = Trace(Ints.zero, List(Butlast(J)), s, List(j), Eps(List(Upd(Ints.lt(j, n), Ints.plus(s, j)))))
      R(List(rule), other) ==> other

    // the conjuncts of a guard that does not match the guard of the expression as a whole follow from it,
    // or are matched against its conjuncts, which instantiates variables that occur only in the guard, here b = n
    test("guard conjuncts"):
      val Xs = Var("Xs", ints)
      val b = Var("b", int)
      val capped = Fun("capped", Nil, Fun.formals(int, ints, int), trace)
      val rule = rw(
        Trace(i, List(Xs), x, List(v), Eps(List(Upd(And(Ints.lt(Ints.zero, v), Ints.le(x, b)), Ints.plus(x, v))))),
        app(capped, i, Xs, b)
      )

      val expr = Trace(Ints.zero, List(Butlast(J)), s, List(j), Eps(List(Upd(And(Ints.le(s, n), Ints.lt(Ints.zero, j)), Ints.plus(s, j)))))
      R(List(rule), expr) ==> app(capped, Ints.zero, Butlast(J), n)

      // the bound must be among the conjuncts of the guard of the expression
      val other = Trace(Ints.zero, List(Butlast(J)), s, List(j), Eps(List(Upd(Ints.lt(Ints.zero, j), Ints.plus(s, j)))))
      R(List(rule), other) ==> other
