package cuvee.test
package util

import utest._

import _root_.util.SCC

object SCCTests extends TestSuite:
  val tests = Tests:
    test("order"):
      // a and b are mutually recursive and refer to c, d is independent, e refers to itself
      val succ = Map("a" -> Set("b", "c"), "b" -> Set("a"), "c" -> Set(), "d" -> Set("x"), "e" -> Set("e"))
      SCC(List("a", "b", "c", "d", "e"), succ) ==> List(List("c"), List("a", "b"), List("d"), List("e"))

    test("empty"):
      SCC(Nil, (_: Int) => Set()) ==> Nil
