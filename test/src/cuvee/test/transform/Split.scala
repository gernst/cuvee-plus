package cuvee.test
package transform

import utest._

import cuvee.core._
import cuvee.transform.{Split => S}

// the obligations of -split hold if and only if the goals do, for the examples verified with -verify
object Split extends TestSuite:
  import cuvee.test.dafny.Verify.expected

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val p = Var("p", Sort.bool)

  val tests = Tests:
    // conjunctions are split, premises and bound variables move into the context, true is dropped
    test("formula"):
      val phi = All(List(x), Imp(And(p, True), And(List(Lt.int(x, y), True, All(List(y), Le.int(x, y))))))
      S.split(Nil, Nil, phi) ==> List(
        All(List(x), Imp(p, Lt.int(x, y))),
        All(List(x, y), Imp(p, Le.int(x, y)))
      )

    // the inner y clashes with the free y of the first obligation, but each obligation binds what it uses
    test("unused bound variables"):
      S.split(Nil, Nil, All(List(x, y), Imp(p, p))) ==> List(Imp(p, p))

    test("examples"):
      for file <- Examples.find(os.sub / "vcgen", "dfy")
      do
        val first = os.read.lines(file).head
        val errors = Examples.errors("-verify", "-split", "-z3", file.toString)
        if expected(first).isEmpty
        then assert(errors.isEmpty)
        else assert(errors.nonEmpty && errors.forall(_ == "goal does not hold"))
