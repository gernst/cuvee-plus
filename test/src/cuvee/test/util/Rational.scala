package cuvee.test
package util

import utest._

import _root_.util.Rational

object RationalTests extends TestSuite:
  val tests = Tests:
    test("normalized"):
      Rational(2, 4) ==> Rational(1, 2)
      Rational(1, -2) ==> Rational(-1, 2)
      Rational(0, 5) ==> Rational(0)

    test("arithmetic"):
      Rational(1, 2) + Rational(1, 3) ==> Rational(5, 6)
      Rational(1, 2) * Rational(2, 3) ==> Rational(1, 3)
      Rational(1, 2) / Rational(1, 4) ==> Rational(2)
      assert(Rational(1, 3) < Rational(1, 2), Rational(1, 2) <= Rational(1, 2))

    test("parse decimal"):
      Rational.decimal("12.345") ==> Rational(12345, 1000)
      Rational.decimal("2") ==> Rational(2)
      Rational.decimal("0.50") ==> Rational(1, 2)

    test("print decimal"):
      Rational(2).decimal ==> Some("2.0")
      Rational(1, 8).decimal ==> Some("0.125")
      Rational(123, 20).decimal ==> Some("6.15")
      Rational(1, 3).decimal ==> None
