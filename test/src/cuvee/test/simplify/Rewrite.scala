package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.Rule
import cuvee.simplify.Context

// single rewrite steps whose input the simplifier would change before the rules apply
// (see examples/smtlib/simplify/rewrite*.smt2 and examples/dafny/simplify/rewrite*.dfy for the others)
object Rewrite extends TestSuite:
  // a rule whose type parameters and variables are the free ones of its left-hand side
  def rw(lhs: Expr, rhs: Expr, cond: Expr = True) =
    Rule(lhs.params, lhs.free, lhs, rhs, cond)

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val a = Var("a", Sort.int)
  val b = Var("b", Sort.int)

  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)
  val g = Fun("g", Nil, Fun.formals(Sort.int), Sort.int)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  // a single step at the top of `expr`, subterms are not rewritten (the simplifier traverses them)
  def R(rules: List[Rule], expr: Expr): Expr =
    R(Context.empty.withRules(rules), expr)

  def R(ctx: Context, expr: Expr): Expr =
    cuvee.simplify.Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, expr)

  val tests = Tests:
    // a variable of the pattern may take the neutral element if the expression is a sum, where 0 is dropped
    test("neutral"):
      val rules = List(rw(app(f, Ints.plus(x, y)), app(g, y)))
      R(rules, app(f, Ints.plus(a, Ints.zero))) ==> app(g, Ints.zero)
      R(rules, app(f, a)) ==> app(f, a)

      // but only if there are fewer summands than variables, x + y matches a + b with x = a or x = b, not x = 0
      val ms = cuvee.simplify.Rewrite.matches(cuvee.Config.default, State.empty, Context.empty, Set(), Set(x, y), Set(), Ints.plus(x, y), None, Map(), Set(), Ints.plus(a, b), Subst.empty)
      ms.map(_.vars(x)) ==> List(a, b)
