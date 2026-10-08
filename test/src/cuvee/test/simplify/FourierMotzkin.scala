package cuvee.test
package simplify

import utest._

import _root_.util.Rational
import cuvee.core._
import cuvee.simplify.Poly
import cuvee.simplify.Constraint
import cuvee.simplify.FourierMotzkin as FM

object FourierMotzkin extends TestSuite:
  val x = Var("x", Sort.real)
  val y = Var("y", Sort.real)
  val z = Var("z", Sort.real)

  def v(x: Var) = Poly.atom(x)
  def c(n: Int) = Poly.const(Rational(n))

  val tests = Tests:
    test("coefficients"):
      val con = Constraint.le(v(x) * Rational(2), v(y) + c(1))
      con.coeff(x) ==> Rational(-2)
      con.coeff(y) ==> Rational(1)
      con.coeff(z) ==> Rational(0)

    // 0 <= x and x <= 1 are satisfiable, x < 0 and 0 < x are not
    test("bounds"):
      assert(FM.satisfiable(List(Constraint.le(c(0), v(x)), Constraint.le(v(x), c(1)))))
      assert(!FM.satisfiable(List(Constraint.lt(v(x), c(0)), Constraint.lt(c(0), v(x)))))
      assert(FM.satisfiable(List(Constraint.le(v(x), c(0)), Constraint.le(c(0), v(x)))))
      assert(!FM.satisfiable(List(Constraint.lt(v(x), c(0)), Constraint.le(c(0), v(x)))))

    // eliminating y from x <= y and y <= z gives x <= z
    test("transitivity"):
      val cs = List(Constraint.le(v(x), v(y)), Constraint.le(v(y), v(z)))
      FM.eliminate(y, cs) ==> List(Constraint.le(v(x), v(z)))

    // strictness propagates to the combination
    test("strict"):
      val cs = List(Constraint.lt(v(x), v(y)), Constraint.le(v(y), v(z)))
      FM.eliminate(y, cs) ==> List(Constraint.lt(v(x), v(z)))

    // rational coefficients: 2x <= 1 and 1 <= 3x is satisfiable (x = 1/2), 2x <= 1 and 2 <= 3x is not
    test("rational"):
      assert(FM.satisfiable(List(Constraint.le(v(x) * Rational(2), c(1)), Constraint.le(c(1), v(x) * Rational(3)))))
      assert(!FM.satisfiable(List(Constraint.le(v(x) * Rational(2), c(1)), Constraint.le(c(2), v(x) * Rational(3)))))

    // x + y <= 1, 0 <= x, 0 <= y, 1 < x + 2y is satisfiable, with 2 < x + 2y it is not
    test("several atoms"):
      val base = List(Constraint.le(v(x) + v(y), c(1)), Constraint.le(c(0), v(x)), Constraint.le(c(0), v(y)))
      assert(FM.satisfiable(base :+ Constraint.lt(c(1), v(x) + v(y) * Rational(2))))
      assert(!FM.satisfiable(base :+ Constraint.lt(c(2), v(x) + v(y) * Rational(2))))

    // constraints without the atom are kept, trivial ones are dropped
    test("other constraints"):
      val cs = List(Constraint.le(c(0), v(z)), Constraint.le(c(0), c(1)), Constraint.le(v(x), c(0)))
      FM.eliminate(x, cs) ==> List(Constraint.le(c(0), v(z)))

    test("nonlinear"):
      val cs = List(Constraint.le(v(x) * v(y), c(1)))
      val msg =
        try
          FM.eliminate(x, cs)
          "no error"
        catch case cuvee.Error(msg, _*) => msg
      msg ==> "constraints are not linear"
