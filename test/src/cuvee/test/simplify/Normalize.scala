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

    // ite is lifted out of atoms, all of its occurrences at once, but not out of binders inside of atoms
    test("lift"):
      val zero = Zero.int
      show(N.lift(Lt.int(Ite(p, x, y), zero))) ==> "if p then x < 0 else y < 0"
      show(N.lift(Imp(q, Lt.int(Ite(p, x, y), Plus.int(Ite(p, x, y), One.int))))) ==> "q ==> (if p then x < x + 1 else y < y + 1)"
      show(N.lift(Lt.int(Ite(p, Ite(q, x, y), y), zero))) ==> "if p then if q then x < 0 else y < 0 else y < 0"
      val inner = Eq(q, Ex(List(x), Lt.int(Ite(Lt.int(x, y), x, y), zero)))
      N.lift(inner) ==> inner
      val bound = All(List(x), Lt.int(Ite(Lt.int(x, y), x, y), zero))
      show(N.lift(bound)) ==> "forall x: int :: if x < y then x < 0 else y < 0"

    // trivial clauses are true
    test("trivial"):
      N(Imp(False, p)) ==> True
      N(Or(p, True)) ==> True

    // conjunctions among the succedents are kept
    test("conjunctions"):
      show(N(Imp(p, And(q, r)))) ==> "p ==> q && r"
