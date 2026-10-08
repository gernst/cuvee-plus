package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.Normalize as N

// formulas are normalized into equivalent clauses forall xs. antecedents ==> succedents
// (see examples/smtlib/simplify/clauses.smt2), ite is lifted out of atoms where clauses are split
object Normalize extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val p = Var("p", Sort.bool)
  val q = Var("q", Sort.bool)
  val r = Var("r", Sort.bool)

  def show(phi: Expr) =
    cuvee.dafny.Printer.lines(phi).mkString(" ").replaceAll(" +", " ")

  val tests = Tests:
    // bound variables are renamed apart from free ones of the same name, which SMT-LIB input cannot write
    test("quantifiers"):
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
