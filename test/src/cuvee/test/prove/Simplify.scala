package cuvee.test
package prove

import utest._

import cuvee.core._
import cuvee.prove.Context

// one-point rule: an equation x == e of a quantified variable x that occurs nowhere else is true,
// negatively below forall and positively below exists
object OnePoint extends TestSuite:
  import cuvee.Config
  import cuvee.prove.Simplify

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val p = Fun("p", Nil, Fun.formals(Sort.int), Sort.bool)
  val q = Var("q", Sort.bool)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)

  def P(e: Expr) = App(p, List(e))

  def simplify(phi: Expr) =
    Simplify.simplify(Config.default, State.empty, Context.empty(State.empty).copy(polarity = Some(true)), phi)

  val tests = Tests:
    test("forall"):
      simplify(All(List(x, y), Imp(Eq(x, Ints.plus(y, Ints.one)), P(y)))) ==> All(List(y), P(y))
      simplify(All(List(x, y), Imp(Eq(Ints.plus(y, Ints.one), x), P(y)))) ==> All(List(y), P(y))
      // forall x. !(x == y) is false
      simplify(All(List(x), Not(Eq(x, y)))) ==> False

    test("exists"):
      simplify(Ex(List(x), And(Eq(x, y), P(y)))) ==> P(y)
      // below a negation, exists is universal
      simplify(Not(Ex(List(x), And(Eq(x, y), P(y))))) ==> Not(P(y))

    // the variable occurs elsewhere, or twice in equations; an arithmetic definition is substituted first
    test("used"):
      val used = All(List(x), Imp(Eq(x, App(f, List(y))), P(x)))
      simplify(used) ==> used
      // an arithmetic definition is not substituted, it is inlined into polynomials only (see Classes.substitute)
      val arithmetic = All(List(x), Imp(Eq(x, Ints.plus(y, Ints.one)), P(x)))
      simplify(arithmetic) ==> arithmetic
      // equations between variables are one class, whose root is the variable of the outer scope, here the free y
      // (see Classes.Order), so the bound x is eliminated
      simplify(All(List(x), Imp(Eq(x, y), P(x)))) ==> P(y)
      val twice = All(List(x), Imp(And(Eq(x, Ints.plus(y, Ints.one)), Eq(x, z)), q))
      assert(simplify(twice) != q)

    // forall x. x == y is not true, and equations in positions without polarity remain
    test("polarity"):
      val positive = All(List(x), Eq(x, Ints.plus(y, Ints.one)))
      simplify(positive) ==> positive
      val neutral = All(List(x), Imp(Eqv(Eq(x, y), q), q))
      assert(simplify(neutral).free.isEmpty || simplify(neutral) != Imp(q, q))
      // the branch of the test x == y has x replaced by the root y of the class, the variable of the outer scope
      simplify(All(List(x), Imp(P(Ite(Eq(x, y), x, z)), q))) ==> All(List(x), Imp(P(Ite(Eq(x, y), y, z)), q))

    // forall distributes over and, exists over or, after which the one-point rule applies to one part
    test("distribute"):
      val e = Ints.plus(y, Ints.one)
      simplify(All(List(x), And(P(x), Imp(Eq(x, e), q)))) ==> And(All(List(x), P(x)), q)
      simplify(Ex(List(x), Or(P(x), And(Eq(x, e), q)))) ==> Or(Ex(List(x), P(x)), q)

    // x cannot be instantiated by e that depends on a variable bound inside the scope of x
    test("scope"):
      val phi = All(List(x), Ex(List(y), Not(Eq(x, y))))
      simplify(phi) ==> phi
      // the variables of one binder are not nested, e depends on one bound before x
      simplify(All(List(y, x), Imp(Eq(x, Ints.plus(y, Ints.one)), P(y)))) ==> All(List(y), P(y))

    // a quantifier in a position without polarity has the one-point rule for its own variables,
    // whereas the variables of let are neither universal nor existential, also below a negation
    test("nested"):
      simplify(Eqv(q, Ex(List(x), And(Eq(x, Ints.plus(y, Ints.one)), P(y))))) ==> Eq(q, P(y))
      val let = Let(List(x), List(Ints.plus(y, Ints.one)), Not(Eq(x, z)))
      simplify(Imp(P(z), let)) ==> Imp(P(z), let)

    // the context does not record the other branch of ite and the dependencies of all
    test("opaque"):
      // only the root y of the class replaces x in the branch where x == y holds
      val branch = All(List(x), Ite(q, Imp(Eq(x, y), P(x)), P(x)))
      simplify(branch) ==> All(List(x), Ite(q, Imp(Eq(x, y), P(y)), P(x)))
      val xs = Var("xs", Sort.seq(Sort.int))
      val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.seq(Sort.int))
      val k = Var("k", Sort.int)
      val invs = All(List(x), Invs(List(App(f, List(x))), List(k), Imp(Eq(x, y), P(k))))
      simplify(invs) ==> invs

// the helpers of the simplifier see variables through their definitions among the assumptions (Context.↑)
object Definitions extends TestSuite:
  import cuvee.Config
  import cuvee.prove.Simplify

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val a = Var("a", Sort.array(Sort.int, Sort.int))
  val b = Var("b", Sort.array(Sort.int, Sort.int))
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)

  def simplify(ctx: Context, expr: Expr, state: State = State.empty) =
    Simplify.simplify(Config.default, state, ctx, expr)

  val tests = Tests:
    // read over write and overwriting of an array defined by a write
    test("arrays"):
      val ctx = Context.empty(State.empty).assume(Eq(a, Store(b, x, y)))
      simplify(ctx, Select(a, x)) ==> y
      simplify(ctx, Store(a, x, z)) ==> Store(b, x, z)
      // other indices only if they are known to differ
      simplify(ctx, Select(a, z)) ==> Select(a, z)
      val ctx_ = Context.empty(State.empty).assume(Eq(a, Store(b, Ints.zero, y)))
      simplify(ctx_, Select(a, Ints.one)) ==> Select(b, Ints.one)

    // lambdas bind their variable, which is renamed apart from the context, are reduced when applied (beta),
    // also when an array is defined by one, and are an array whose elements they select (eta)
    test("lambdas"):
      val typ = Sort.array(Sort.int, Sort.int)
      val ctx = Context.empty(State.empty).assume(Eq(x, Ints.one))
      val Lam(List(x_), body, _) = simplify(ctx, Lam(List(x), Ints.plus(x, y), typ)): @unchecked
      assert(x_ != x)
      body ==> Ints.plus(x_, y)
      simplify(Context.empty(State.empty), Lam(List(x), Ints.plus(x, Ints.zero), typ)) ==> Lam(List(x), x, typ)
      simplify(Context.empty(State.empty), Lam(List(x), Select(a, x), typ)) ==> a
      simplify(Context.empty(State.empty), Select(Lam(List(x), Ints.plus(x, y), typ), z)) ==> Ints.plus(y, z)
      simplify(Context.empty(State.empty).assume(Eq(a, Lam(List(x), Ints.plus(x, y), typ))), Select(a, z)) ==> Ints.plus(y, z)
      // extensionality: equal lambdas have equal bodies, the equation of an array and a lambda is kept
      simplify(Context.empty(State.empty), Eq(Lam(List(x), Ints.plus(x, y), typ), Lam(List(z), Ints.plus(y, z), typ))) ==> True
      simplify(Context.empty(State.empty), Eq(Lam(List(x), x, typ), Lam(List(z), y, typ))) ==> All(List(x), Eq(x, y))
      simplify(Context.empty(State.empty), Eq(a, Lam(List(x), x, typ))) ==> Eq(a, Lam(List(x), x, typ))

    // lambdas of function type are reduced when applied (beta), also when a function value is defined by one,
    // are the function value that they apply (eta), and are equal if their bodies are, for several variables
    test("functions"):
      val fun = Arrow(List(Sort.int, Sort.int), Sort.int)
      val g = Var("g", fun)
      val add = Lam(List(x, y), Ints.plus(x, y), fun)
      simplify(Context.empty(State.empty), Apply(add, List(z, Ints.one))) ==> Ints.plus(z, Ints.one)
      simplify(Context.empty(State.empty).assume(Eq(g, add)), Apply(g, List(z, z))) ==> Ints.times(Lit(BigInt(2), Sort.int), z)
      simplify(Context.empty(State.empty), Lam(List(x, y), Apply(g, List(x, y)), fun)) ==> g
      simplify(Context.empty(State.empty), Lam(List(x, y), Apply(g, List(y, x)), fun)) ==> Lam(List(x, y), Apply(g, List(y, x)), fun)
      simplify(Context.empty(State.empty), Eq(add, Lam(List(y, z), Ints.plus(z, y), fun))) ==> True
      simplify(Context.empty(State.empty), Eq(add, Lam(List(y, z), y, fun))) ==> All(List(y), Eq(y, Ints.zero))

    // testers of a variable defined by a constructor application, also with a type annotation
    test("testers"):
      import cuvee.test.Matching.{state, list, nil, cons, xs, ys}
      val ctx = Context.empty(State.empty).assume(Eq(xs, App(cons, List(x, ys))))
      simplify(ctx, Is(xs, cons), state) ==> True
      simplify(ctx, Is(xs, nil), state) ==> False
      val ctx_ = Context.empty(State.empty).assume(Eq(xs, As(App(cons, List(x, ys)), list)))
      simplify(ctx_, Is(xs, cons), state) ==> True

    // variables with the same definition are equal
    test("equations"):
      val ctx = Context.empty(State.empty).assume(Eq(x, App(f, List(y)))).assume(Eq(z, App(f, List(y))))
      simplify(ctx, Eq(x, z)) ==> True

// formulas are decided by whether denying or assuming them makes the theories of the context inconsistent
object Decisions extends TestSuite:
  import cuvee.Config
  import cuvee.prove.Simplify

  val n = Var("n", Sort.int)
  val p = Var("p", Sort.bool)

  def lit(k: Int) = Lit(BigInt(k), Sort.int)

  def simplify(ctx: Context, expr: Expr) =
    Simplify.simplify(Config.default, State.empty, ctx, expr)

  val tests = Tests:
    // the bounds of the loop counter in the goal of array_1-1
    test("differences"):
      val ctx = Context.empty(State.empty).assume(Ints.le(lit(1024), n)).assume(Ints.lt(n, lit(1025)))
      simplify(ctx, Eq(n, lit(1024))) ==> True
      simplify(ctx, Eq(n, Ints.zero)) ==> False
      simplify(ctx, Ints.le(Ints.zero, n)) ==> True
      simplify(ctx, Ints.lt(n, lit(1024))) ==> False
      simplify(Context.empty(State.empty).assume(Ints.le(lit(1024), n)), Eq(n, lit(1024))) ==> Eq(n, lit(1024))

    // the facts themselves, also by the negation in normal form
    test("facts"):
      simplify(Context.empty(State.empty).assume(p), p) ==> True
      simplify(Context.empty(State.empty).deny(p), p) ==> False
      simplify(Context.empty(State.empty).deny(p), Not(p)) ==> True
      val r = Var("r", Sort.real)
      simplify(Context.empty(State.empty).deny(Reals.le(r, Reals.zero)), Reals.lt(Reals.zero, r)) ==> True
      // equations of variables are substituted rather than recorded, they still conflict with the conclusions
      val m = Var("m", Sort.int)
      simplify(Context.empty(State.empty).deny(Eq(n, m)), Eq(n, m)) ==> False
      simplify(Context.empty(State.empty).deny(Eq(n, lit(40))), Eq(n, lit(40))) ==> False

    // on Int, comparisons are rounded by the gcd of the coefficients
    test("rounding"):
      val twice = Ints.times(lit(2), n)
      simplify(Context.empty(State.empty), Ints.le(Ints.plus(twice, Ints.one), lit(52))) ==> Ints.le(n, lit(25))
      simplify(Context.empty(State.empty), Ints.lt(twice, lit(52))) ==> Ints.lt(n, lit(26))
      simplify(Context.empty(State.empty), Ints.le(lit(1000000), twice)) ==> Ints.le(lit(500000), n)

    // a bound n <= m is an equation if m <= n is known, which is then substituted
    test("bounds to equations"):
      simplify(Context.empty(State.empty).assume(Ints.le(n, Ints.zero)), Ints.le(Ints.zero, n)) ==> Eq(Ints.zero, n)
      val x = Var("x", Sort.int)
      val goal = All(List(x), Not(And(List(Ints.le(Ints.zero, x), Ints.le(x, Ints.zero), Not(Eq(Ints.mod(x, lit(2)), Ints.zero))))))
      simplify(Context.empty(State.empty).copy(polarity = Some(true)), goal) ==> True

    // a bound n <= m becomes strict if n != m is known
    test("disequations"):
      val ctx = Context.empty(State.empty).deny(Eq(n, lit(40)))
      simplify(ctx, Ints.le(n, lit(40))) ==> Ints.lt(n, lit(40))
      simplify(Context.empty(State.empty).deny(Eq(n, Ints.zero)), Ints.le(Ints.zero, n)) ==> Ints.lt(Ints.zero, n)
      simplify(ctx, Ints.le(n, lit(41))) ==> Ints.le(n, lit(41))

    // the coefficients and the constant of a polynomial modulo a literal
    test("modulo"):
      simplify(Context.empty(State.empty), Ints.mod(Ints.times(lit(2), n), lit(2))) ==> Ints.zero
      simplify(Context.empty(State.empty), Ints.mod(Ints.plus(Ints.times(lit(2), n), lit(11)), lit(2))) ==> Ints.one
      simplify(Context.empty(State.empty), Ints.mod(Ints.plus(Ints.times(lit(3), n), Ints.one), lit(2))) ==> Ints.mod(Ints.plus(n, Ints.one), lit(2))
      simplify(Context.empty(State.empty), Ints.mod(n, lit(2))) ==> Ints.mod(n, lit(2))

    // earlier and maps commute, also for the cases of an update
    test("earlier of maps"):
      val k = Var("k", Sort.int)
      val v = Var("v", Sort.int)
      val xs = Var("xs", Sort.list(Sort.int))
      simplify(Context.empty(State.empty), Earlier(k, Maps(List(xs), List(v), Ints.plus(v, Ints.one)))) ==>
        Ints.plus(Earlier(k, xs), Ints.one)
      val cases = Eps(List(Upd(Ints.lt(v, Ints.zero), Ints.zero), Upd(Ints.le(Ints.zero, v), v)))
      simplify(Context.empty(State.empty), Earlier(k, Maps(List(xs), List(v), cases))) ==>
        Eps(List(Upd(Ints.lt(Earlier(k, xs), Ints.zero), Ints.zero), Upd(Ints.le(Ints.zero, Earlier(k, xs)), Earlier(k, xs))))

    // earlier moves into both branches of ite and into the body of let, whose bound variables avoid capture
    test("earlier of ite and let"):
      val j = Var("j", Sort.int)
      val p = Var("p", Sort.bool)
      val xs = Var("xs", Sort.list(Sort.int))
      val ys = Var("ys", Sort.list(Sort.int))
      simplify(Context.empty(State.empty), Earlier(j, Ite(p, xs, ys))) ==> Ite(p, Earlier(j, xs), Earlier(j, ys))
      val k = Var("k", Sort.int)
      val inner = Let(List(j), List(k), Ite(Eq(j, Ints.zero), xs, ys))
      val Let(List(j_), List(k_), body) = simplify(Context.empty(State.empty), Earlier(j, inner)): @unchecked
      assert(j_ != j)
      k_ ==> k
      body ==> Ite(Eq(j_, Ints.zero), Earlier(j, xs), Earlier(j, ys))

    // the guards of nested choices are combined
    test("nested choices"):
      val x = Var("x", Sort.int)
      val y = Var("y", Sort.int)
      val p = Var("p", Sort.bool)
      val q = Var("q", Sort.bool)
      val z = Var("z", Sort.int)
      val inner = Eps(List(Upd(q, x), Upd(Not(q), y)))
      simplify(Context.empty(State.empty), Eps(List(Upd(p, inner), Upd(Not(p), z)))) ==>
        Eps(List(Upd(And(p, q), x), Upd(And(p, Not(q)), y), Upd(Not(p), z)))

    // cases with equal results are merged by the disjunction of their guards,
    // and a single case is its result, since the guards are complete
    test("equal results"):
      val x = Var("x", Sort.int)
      val y = Var("y", Sort.int)
      val p = Var("p", Sort.bool)
      val q = Var("q", Sort.bool)
      val r = Var("r", Sort.bool)
      simplify(Context.empty(State.empty), Eps(List(Upd(p, x), Upd(q, y), Upd(r, x)))) ==> Eps(List(Upd(Or(p, r), x), Upd(q, y)))
      simplify(Context.empty(State.empty), Eps(List(Upd(p, x), Upd(q, x)))) ==> x

    // an inconsistent context decides formulas by polarity only, not by the theories
    test("inconsistent"):
      val ctx = Context.empty(State.empty).assume(Ints.le(Ints.one, n)).assume(Ints.le(n, Ints.zero))
      assert(ctx.inconsistent)
      assert(!ctx.implied(p))
      assert(!ctx.denied(p))
