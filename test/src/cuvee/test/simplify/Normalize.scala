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
    // bound variables are renamed apart from free ones of the same name, which SMT-LIB input cannot write;
    // the index of the fresh name depends on the fresh names created before in the same run, e.g. by other tests
    test("quantifiers"):
      val shown = show(N(Imp(Ex(List(x), Ints.lt(x, y)), Ints.le(x, y))))
      shown.matches("forall x[₀-₉]+: int :: x[₀-₉]+ < y ==> x <= y") ==> true

    // ite is lifted out of atoms, all of its occurrences at once, but not out of binders inside of atoms
    test("lift"):
      val zero = Ints.zero
      show(N.lift(Ints.lt(Ite(p, x, y), zero))) ==> "if p then x < 0 else y < 0"
      show(N.lift(Imp(q, Ints.lt(Ite(p, x, y), Ints.plus(Ite(p, x, y), Ints.one))))) ==> "q ==> (if p then x < x + 1 else y < y + 1)"
      show(N.lift(Ints.lt(Ite(p, Ite(q, x, y), y), zero))) ==> "if p then if q then x < 0 else y < 0 else y < 0"
      val inner = Eq(q, Ex(List(x), Ints.lt(Ite(Ints.lt(x, y), x, y), zero)))
      N.lift(inner) ==> inner
      val bound = All(List(x), Ints.lt(Ite(Ints.lt(x, y), x, y), zero))
      show(N.lift(bound)) ==> "forall x: int :: if x < y then x < 0 else y < 0"
