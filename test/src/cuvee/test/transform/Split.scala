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

    // each obligation binds the variables that it uses
    test("unused bound variables"):
      S.split(Nil, Nil, All(List(x, y), Imp(p, Lt.int(x, x)))) ==> List(All(List(x), Imp(p, Lt.int(x, x))))

    // a succedent that is also an antecedent makes an obligation true
    test("trivial"):
      S.split(Nil, Nil, All(List(x, y), Imp(p, p))) ==> Nil
      S.split(Nil, Nil, Imp(False, p)) ==> Nil

    // disjunctions in the conclusion are succedents, negated conclusions are antecedents
    test("disjunctions"):
      val q = Var("q", Sort.bool)
      S.split(Nil, Nil, Or(Not(p), q)) ==> List(Imp(p, q))

    // if-then-else in the terms of atoms is lifted and split by its test
    test("lifted"):
      val goal = Assert(Goal, Nil, Lt.int(Ite(p, x, y), Zero.int), Attrs.empty)
      S.split(goal) ==> List(
        Assert(Goal, Nil, Imp(p, Lt.int(x, Zero.int)), Attrs.empty),
        Assert(Goal, Nil, Imp(Not(p), Lt.int(y, Zero.int)), Attrs.empty)
      )

    // disjunctions and if-then-else among the antecedents are split into cases
    test("cases"):
      val q = Var("q", Sort.bool)
      S.split(Nil, Nil, Imp(Or(p, q), Lt.int(x, y))) ==> List(Imp(p, Lt.int(x, y)), Imp(q, Lt.int(x, y)))
      S.split(Nil, Nil, Ite(p, q, Lt.int(x, y))) ==> List(Imp(p, q), Imp(Not(p), Lt.int(x, y)))

    // existential quantifiers among the antecedents bind their variables
    test("existential antecedents"):
      S.split(Nil, Nil, Imp(Ex(List(x), Lt.int(x, y)), Lt.int(Zero.int, y))) ==>
        List(All(List(x), Imp(Lt.int(x, y), Lt.int(Zero.int, y))))

    test("examples"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filter(Examples.supported)
      do
        val first = os.read.lines(file).head
        val errors = Examples.errors("-verify", "-split", "-z3", file.toString)
        if expected(first).isEmpty
        then assert(errors.isEmpty)
        else assert(errors.nonEmpty && errors.forall(_ == "goal does not hold"))
