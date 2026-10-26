package cuvee.test
package prove

import utest._

import cuvee.core._
import cuvee.prove.Classes

// the congruence closure of the engine of -prove
object ClassesTests extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)
  val g = Fun("g", Nil, Fun.formals(Sort.int, Sort.int), Sort.int)
  val c = Fun("c", Nil, Fun.formals(Sort.int), Sort.int)
  val d = Fun("d", Nil, Fun.formals(Sort.int), Sort.int)

  def lit(k: Int) = Lit(BigInt(k), Sort.int)
  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  given Classes.Order = Classes.Order(Classes.rank(_ => (0, 0)))

  def facts(phis: Expr*) =
    phis.foldLeft(Classes.empty(Set(c, d)))(_.assume(_))

  val tests = Tests:
    test("transitivity"):
      val cl = facts(Eq(x, y), Eq(y, z))
      assert(cl.equal(x, z))
      assert(!cl.equal(x, lit(1)))
      assert(cl.deny(Eq(x, z)).inconsistent)
      assert(!cl.inconsistent)

    // f(x) == f(y) follows from x == y, also for applications registered later
    test("congruence"):
      val cl = facts(Eq(x, y)).add(app(f, x)).add(app(f, y))
      assert(cl.equal(app(f, x), app(f, y)))
      val cl_ = facts(Not(Eq(app(g, x, z), app(g, y, z)))).assume(Eq(x, y))
      assert(cl_.inconsistent)

    // the definitions of a variable are the non-variable members of its class, in both orientations
    test("definitions"):
      val cl = facts(Eq(app(f, x), y), Eq(z, y))
      assert(cl.defs(z) == List(app(f, x)))
      assert(cl.defs(y) == List(app(f, x)))
      assert(cl.normalize(z).isInstanceOf[Var])
      val cl_ = cl.assume(Eq(y, lit(3)))
      assert(cl_.normalize(z) == lit(3))

    // two literals or two constructors in a class are inconsistent
    test("clashes"):
      assert(facts(Eq(x, lit(1)), Eq(x, lit(2))).inconsistent)
      assert(facts(Eq(x, app(c, y)), Eq(x, app(d, y))).inconsistent)
      assert(!facts(Eq(x, app(c, y)), Eq(x, app(c, z))).inconsistent)
      assert(!facts(Eq(x, app(f, y)), Eq(x, app(g, y, z))).inconsistent)

    // the canonical form of the members of a class is the same, its root
    test("canonical"):
      val cl = facts(Eq(z, y), Eq(x, z))
      assert(cl.normalize(x) == cl.normalize(y) && cl.normalize(y) == cl.normalize(z))
