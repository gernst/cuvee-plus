package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.Ctx

// equations among the assumptions: between variables in su, others in eq if they are not recursive
object Context extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)

  val tests = Tests:
    test("variables"):
      val ctx = Ctx.empty.assume(Eq(x, y))
      ctx.su ==> Map(x -> y)
      ctx.eq ==> Map()
      ctx.assms ==> Nil

    // equations with literals are substituted like those between variables
    test("literals"):
      val one = One.int
      Ctx.empty.assume(Eq(x, one)).su ==> Map(x -> one)
      Ctx.empty.assume(Eq(one, x)).su ==> Map(x -> one)
      Ctx.empty.assume(Eq(x, one)).assms ==> Nil
      val ctx = Ctx.empty.assume(Eq(x, one))
      cuvee.simplify.Simplify.simplify(cuvee.Config.default, State.empty, ctx, Plus.int(x, y)) ==> Plus.int(y, one)

    test("equations"):
      val e = Plus.int(y, One.int)
      Ctx.empty.assume(Eq(x, e)).eq ==> Map(x -> e)
      Ctx.empty.assume(Eq(e, x)).eq ==> Map(x -> e)
      // the equation is still an assumption
      Ctx.empty.assume(Eq(x, e)).assms ==> List(Eq(x, e))
      // the first equation of a variable is kept
      Ctx.empty.assume(Eq(x, e)).assume(Eq(x, z)).eq ==> Map(x -> e)

    test("recursive"):
      val e = Plus.int(x, One.int)
      Ctx.empty.assume(Eq(x, e)).eq ==> Map()

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

    // the variable occurs elsewhere, or twice in equations
    test("used"):
      val used = All(List(x), Imp(Eq(x, Plus.int(y, One.int)), P(x)))
      simplify(used) ==> used
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

    // x cannot be instantiated by e that depends on a variable bound inside the scope of x
    test("scope"):
      val phi = All(List(x), Ex(List(y), Not(Eq(x, y))))
      simplify(phi) ==> phi

    // the context does not record the other branch of ite and the dependencies of all
    test("opaque"):
      val branch = All(List(x), Ite(q, Imp(Eq(x, y), P(y)), P(x)))
      simplify(branch) ==> branch
      val xs = Var("xs", Sort.seq(Sort.int))
      val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.seq(Sort.int))
      val k = Var("k", Sort.int)
      val invs = All(List(x), Invs(List(App(f, List(x))), List(k), Imp(Eq(x, y), P(k))))
      simplify(invs) ==> invs
