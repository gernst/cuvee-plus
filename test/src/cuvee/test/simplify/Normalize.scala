package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.{Normalize => N}

// formulas are normalized into equivalent clauses forall xs. antecedents ==> succedents
object Normalize extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val p = Var("p", Sort.bool)
  val q = Var("q", Sort.bool)
  val r = Var("r", Sort.bool)

  def show(phi: Expr) =
    cuvee.dafny.Printer.lines(phi).mkString(" ").replaceAll(" +", " ")

  val tests = Tests:
    // nested implications and conjunctions among the antecedents are flattened
    test("implications"):
      show(N(Imp(And(p, q), Imp(r, Lt.int(x, y))))) ==> "p && q && r ==> x < y"

    // disjunctions among the succedents, negations move to the other side
    test("disjunctions"):
      show(N(Or(Not(And(p, q)), r))) ==> "p && q ==> r"
      show(N(Imp(Not(Or(p, q)), r))) ==> "p || q || r"

    // existential antecedents and universal succedents bind their variables in the prefix
    test("quantifiers"):
      val z = Var("z", Sort.int)
      show(N(Imp(Ex(List(x), Lt.int(x, z)), All(List(y), Le.int(z, y))))) ==> "forall x: int, y: int :: x < z ==> z <= y"
      // bound variables are renamed apart from free ones of the same name
      show(N(Imp(Ex(List(x), Lt.int(x, y)), Le.int(x, y)))) ==> "forall x₁: int :: x₁ < y ==> x <= y"

    // trivial clauses are true
    test("trivial"):
      N(Imp(False, p)) ==> True
      N(Or(p, True)) ==> True

    // conjunctions among the succedents are kept
    test("conjunctions"):
      show(N(Imp(p, And(q, r)))) ==> "p ==> q && r"
