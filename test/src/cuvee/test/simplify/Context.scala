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
