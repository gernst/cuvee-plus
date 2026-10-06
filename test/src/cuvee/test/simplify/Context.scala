package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.Ctx

// equations among the assumptions: between variables in replace, others in chain if they are not recursive
// and their right-hand side is not an arithmetic operation
object Context extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)

  val tests = Tests:
    test("variables"):
      val ctx = Ctx.empty.assume(Eq(x, y))
      ctx.chains.replace ==> Map(x -> y)
      ctx.chains.chain ==> Map()
      ctx.facts.assms ==> Nil

    // equations with literals are substituted like those between variables
    test("literals"):
      val one = One.int
      Ctx.empty.assume(Eq(x, one)).chains.replace ==> Map(x -> one)
      Ctx.empty.assume(Eq(one, x)).chains.replace ==> Map(x -> one)
      Ctx.empty.assume(Eq(x, one)).facts.assms ==> Nil
      val ctx = Ctx.empty.assume(Eq(x, one))
      cuvee.simplify.Simplify.simplify(cuvee.Config.default, State.empty, ctx, Plus.int(x, y)) ==> Plus.int(y, one)

    test("equations"):
      val e = App(f, List(y))
      Ctx.empty.assume(Eq(x, e)).chains.chain ==> Map(x -> e)
      Ctx.empty.assume(Eq(e, x)).chains.chain ==> Map(x -> e)
      // the equation is still an assumption
      Ctx.empty.assume(Eq(x, e)).facts.assms ==> List(Eq(x, e))
      // the first equation of a variable is kept
      Ctx.empty.assume(Eq(x, e)).assume(Eq(x, z)).chains.chain ==> Map(x -> e)

    test("recursive"):
      val e = App(f, List(x))
      Ctx.empty.assume(Eq(x, e)).chains.chain ==> Map()

    // arithmetic equations are solved for a variable with coefficient 1 or -1 and substituted, the substitution stays acyclic
    test("arithmetic"):
      val e = Plus.int(y, One.int)
      val two = Lit(BigInt(2), Sort.int)
      val forty = Lit(BigInt(40), Sort.int)
      Ctx.empty.assume(Eq(x, e)).chains.chain ==> Map()
      Ctx.empty.assume(Eq(x, e)).chains.replace ==> Map(x -> e)
      Ctx.empty.assume(Eq(x, e)).facts.assms ==> Nil
      Ctx.empty.assume(Eq(Plus.int(x, y), forty)).chains.replace ==> Map(x -> Plus.int(UMinus.int(y), forty))
      // the first variable in the order of the monomials is solved for
      val ctx = Ctx.empty.assume(Eq(y, Plus.int(x, One.int)))
      ctx.chains.replace ==> Map(x -> Plus.int(y, Lit(BigInt(-1), Sort.int)))
      // x is replaced already, z == x + 2 is solved neither for x nor for z, whose solution contains x
      ctx.assume(Eq(z, Plus.int(x, two))).chains.replace ==> ctx.chains.replace
      // y occurs in a replacement, y == z + 2 is solved for z instead
      ctx.assume(Eq(y, Plus.int(z, two))).chains.replace ==> ctx.chains.replace + (z -> Plus.int(y, Lit(BigInt(-2), Sort.int)))

// one-point rule: an equation x == e of a quantified variable x that occurs nowhere else is true,
// negatively below forall and positively below exists
object OnePoint extends TestSuite:
  import cuvee.Config
  import cuvee.simplify.Simplify

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val p = Fun("p", Nil, Fun.formals(Sort.int), Sort.bool)
  val q = Var("q", Sort.bool)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)

  def P(e: Expr) = App(p, List(e))

  def simplify(phi: Expr) =
    Simplify.simplify(Config.default, State.empty, Ctx.pos, phi)

  val tests = Tests:
    test("forall"):
      simplify(All(List(x, y), Imp(Eq(x, Plus.int(y, One.int)), P(y)))) ==> All(List(y), P(y))
      simplify(All(List(x, y), Imp(Eq(Plus.int(y, One.int), x), P(y)))) ==> All(List(y), P(y))
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
      simplify(All(List(x), Imp(Eq(x, Plus.int(y, One.int)), P(x)))) ==> P(Plus.int(y, One.int))
      // equations between variables substitute first, after which the equation is unused
      simplify(All(List(x), Imp(Eq(x, y), P(x)))) ==> P(y)
      val twice = All(List(x), Imp(And(Eq(x, Plus.int(y, One.int)), Eq(x, z)), q))
      assert(simplify(twice) != q)

    // forall x. x == y is not true, and equations in positions without polarity remain
    test("polarity"):
      val positive = All(List(x), Eq(x, Plus.int(y, One.int)))
      simplify(positive) ==> positive
      val neutral = All(List(x), Imp(Eqv(Eq(x, y), q), q))
      assert(simplify(neutral).free.isEmpty || simplify(neutral) != Imp(q, q))
      simplify(All(List(x), Imp(P(Ite(Eq(x, y), y, z)), q))) ==> All(List(x), Imp(P(Ite(Eq(x, y), y, z)), q))

    // forall distributes over and, exists over or, after which the one-point rule applies to one part
    test("distribute"):
      val e = Plus.int(y, One.int)
      simplify(All(List(x), And(P(x), Imp(Eq(x, e), q)))) ==> And(All(List(x), P(x)), q)
      simplify(Ex(List(x), Or(P(x), And(Eq(x, e), q)))) ==> Or(Ex(List(x), P(x)), q)

    // x cannot be instantiated by e that depends on a variable bound inside the scope of x
    test("scope"):
      val phi = All(List(x), Ex(List(y), Not(Eq(x, y))))
      simplify(phi) ==> phi
      // the variables of one binder are not nested, e depends on one bound before x
      simplify(All(List(y, x), Imp(Eq(x, Plus.int(y, One.int)), P(y)))) ==> All(List(y), P(y))

    // a quantifier in a position without polarity has the one-point rule for its own variables,
    // whereas the variables of let are neither universal nor existential, also below a negation
    test("nested"):
      simplify(Eqv(q, Ex(List(x), And(Eq(x, Plus.int(y, One.int)), P(y))))) ==> Eq(q, P(y))
      val let = Let(List(x), List(Plus.int(y, One.int)), Not(Eq(x, z)))
      simplify(Imp(P(z), let)) ==> Imp(P(z), let)

    // the context does not record the other branch of ite and the dependencies of all
    test("opaque"):
      val branch = All(List(x), Ite(q, Imp(Eq(x, y), P(y)), P(x)))
      simplify(branch) ==> branch
      val xs = Var("xs", Sort.seq(Sort.int))
      val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.seq(Sort.int))
      val k = Var("k", Sort.int)
      val invs = All(List(x), Invs(List(App(f, List(x))), List(k), Imp(Eq(x, y), P(k))))
      simplify(invs) ==> invs

// the helpers of the simplifier see variables through their definitions among the assumptions (Ctx.↑)
object Definitions extends TestSuite:
  import cuvee.Config
  import cuvee.simplify.Simplify

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val a = Var("a", Sort.array(Sort.int, Sort.int))
  val b = Var("b", Sort.array(Sort.int, Sort.int))
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)

  def simplify(ctx: Ctx, expr: Expr, state: State = State.empty) =
    Simplify.simplify(Config.default, state, ctx, expr)

  val tests = Tests:
    // read over write and overwriting of an array defined by a write
    test("arrays"):
      val ctx = Ctx.empty.assume(Eq(a, Store(b, x, y)))
      simplify(ctx, Select(a, x)) ==> y
      simplify(ctx, Store(a, x, z)) ==> Store(b, x, z)
      // other indices only if they are known to differ
      simplify(ctx, Select(a, z)) ==> Select(a, z)
      val ctx_ = Ctx.empty.assume(Eq(a, Store(b, Zero.int, y)))
      simplify(ctx_, Select(a, One.int)) ==> Select(b, One.int)

    // testers of a variable defined by a constructor application, also with a type annotation
    test("testers"):
      import cuvee.test.Matching.{state, list, nil, cons, xs, ys}
      val ctx = Ctx.empty.assume(Eq(xs, App(cons, List(x, ys))))
      simplify(ctx, Is(xs, cons), state) ==> True
      simplify(ctx, Is(xs, nil), state) ==> False
      val ctx_ = Ctx.empty.assume(Eq(xs, As(App(cons, List(x, ys)), list)))
      simplify(ctx_, Is(xs, cons), state) ==> True

    // variables with the same definition are equal
    test("equations"):
      val ctx = Ctx.empty.assume(Eq(x, App(f, List(y)))).assume(Eq(z, App(f, List(y))))
      simplify(ctx, Eq(x, z)) ==> True

// formulas are decided by whether denying or assuming them makes the theories of the context inconsistent
object Decisions extends TestSuite:
  import cuvee.Config
  import cuvee.simplify.Simplify

  val n = Var("n", Sort.int)
  val p = Var("p", Sort.bool)

  def lit(k: Int) = Lit(BigInt(k), Sort.int)

  def simplify(ctx: Ctx, expr: Expr) =
    Simplify.simplify(Config.default, State.empty, ctx, expr)

  val tests = Tests:
    // the bounds of the loop counter in the goal of array_1-1
    test("differences"):
      val ctx = Ctx.empty.assume(Le.int(lit(1024), n)).assume(Lt.int(n, lit(1025)))
      simplify(ctx, Eq(n, lit(1024))) ==> True
      simplify(ctx, Eq(n, Zero.int)) ==> False
      simplify(ctx, Le.int(Zero.int, n)) ==> True
      simplify(ctx, Lt.int(n, lit(1024))) ==> False
      simplify(Ctx.empty.assume(Le.int(lit(1024), n)), Eq(n, lit(1024))) ==> Eq(n, lit(1024))

    // the facts themselves, also by the negation in normal form
    test("facts"):
      simplify(Ctx.empty.assume(p), p) ==> True
      simplify(Ctx.empty.deny(p), p) ==> False
      simplify(Ctx.empty.deny(p), Not(p)) ==> True
      val r = Var("r", Sort.real)
      simplify(Ctx.empty.deny(Le.real(r, Zero.real)), Lt.real(Zero.real, r)) ==> True
      // equations of variables are substituted rather than recorded, they still conflict with the conclusions
      val m = Var("m", Sort.int)
      simplify(Ctx.empty.deny(Eq(n, m)), Eq(n, m)) ==> False
      simplify(Ctx.empty.deny(Eq(n, lit(40))), Eq(n, lit(40))) ==> False

    // on Int, comparisons are rounded by the gcd of the coefficients
    test("rounding"):
      val twice = Times.int(lit(2), n)
      simplify(Ctx.empty, Le.int(Plus.int(twice, One.int), lit(52))) ==> Le.int(n, lit(25))
      simplify(Ctx.empty, Lt.int(twice, lit(52))) ==> Lt.int(n, lit(26))
      simplify(Ctx.empty, Le.int(lit(1000000), twice)) ==> Le.int(lit(500000), n)

    // a bound n <= m becomes strict if n != m is known
    test("disequations"):
      val ctx = Ctx.empty.deny(Eq(n, lit(40)))
      simplify(ctx, Le.int(n, lit(40))) ==> Lt.int(n, lit(40))
      simplify(Ctx.empty.deny(Eq(n, Zero.int)), Le.int(Zero.int, n)) ==> Lt.int(Zero.int, n)
      simplify(ctx, Le.int(n, lit(41))) ==> Le.int(n, lit(41))

    // the coefficients and the constant of a polynomial modulo a literal
    test("modulo"):
      simplify(Ctx.empty, Mod.int(Times.int(lit(2), n), lit(2))) ==> Zero.int
      simplify(Ctx.empty, Mod.int(Plus.int(Times.int(lit(2), n), lit(11)), lit(2))) ==> One.int
      simplify(Ctx.empty, Mod.int(Plus.int(Times.int(lit(3), n), One.int), lit(2))) ==> Mod.int(Plus.int(n, One.int), lit(2))
      simplify(Ctx.empty, Mod.int(n, lit(2))) ==> Mod.int(n, lit(2))

    // an inconsistent context decides formulas by polarity only, not by the theories
    test("inconsistent"):
      val ctx = Ctx.empty.assume(Le.int(One.int, n)).assume(Le.int(n, Zero.int))
      assert(ctx.inconsistent)
      assert(!ctx.implied(p, Not(p)))
      assert(!ctx.denied(p, Not(p)))
