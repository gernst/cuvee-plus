package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.Rule
import cuvee.simplify.Simplify
import cuvee.simplify.Context

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
  val abs = Fun("abs", Nil, Fun.formals(Sort.int), Sort.int)
  val q = Fun("q", Nil, Fun.formals(Sort.int, Sort.int), Sort.bool)

  // polymorphic lists, length(cons(x, xs)) = length(xs) + 1
  val p = Param.a
  val list = Sort(Con("List", 1), List(p))
  val nil = Fun("nil", List(p), Nil, list)
  val cons = Fun("cons", List(p), Fun.formals(p, list), list)
  val length = Fun("length", List(p), Fun.formals(list), Sort.int)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  // a single step at the top of `expr`, subterms are not rewritten (the simplifier traverses them)
  def R(rules: List[Rule], expr: Expr): Expr =
    R(Context.empty.withRules(rules), expr)

  def R(ctx: Context, expr: Expr): Expr =
    cuvee.simplify.Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, expr)

  val tests = Tests:
    test("plain"):
      val rules = List(rw(app(f, app(g, x)), x), rw(Plus.int(x, Zero.int), x))
      R(rules, app(f, app(g, Plus.int(a, Zero.int)))) ==> Plus.int(a, Zero.int)
      R(rules, Plus.int(app(f, app(g, a)), Zero.int)) ==> app(f, app(g, a))

    // the variables of a rule must be instantiated consistently
    test("nonlinear"):
      val rules = List(rw(Minus.int(x, x), Zero.int))
      R(rules, Minus.int(a, a)) ==> Zero.int
      R(rules, Minus.int(a, b)) ==> Minus.int(a, b)

    // equations match in either orientation
    test("symmetric equations"):
      val rules = List(rw(Eq(app(f, x), y), True))
      R(rules, Eq(app(f, a), b)) ==> True
      R(rules, Eq(b, app(f, a))) ==> True
      R(rules, Eq(a, b)) ==> Eq(a, b)

    // the first rule that applies is used, at the top only
    test("order"):
      val rules = List(rw(app(f, x), app(g, x)), rw(app(f, x), x))
      R(rules, app(f, app(f, a))) ==> app(g, app(f, a))

    // the type parameters are instantiated, here with Int
    test("polymorphic"):
      val xs = Var("xs", list)
      val rules = List(
        rw(app(length, App(nil, Nil, list, Nil)), Zero.int),
        rw(app(length, app(cons, Var("y", p), xs)), Plus.int(app(length, xs), One.int))
      )

      val ints = Sort(Con("List", 1), List(Sort.int))
      val nil_ = App(nil, Nil, ints, Nil)
      val expr = app(length, app(cons, a, app(cons, b, nil_)))
      R(rules, expr) ==> Plus.int(app(length, app(cons, b, nil_)), One.int)
      R(rules, app(length, nil_)) ==> Zero.int

    // function definitions with :rw whose body is a match on a parameter give one rule per case
    // (see examples/simplify/definitions*.dfy for their application)
    test("definitions"):
      val file = Examples.root / "simplify" / "definitions.dfy"
      val rules = cuvee.simplify.Rules.from(State.empty, Examples.input(file.toString))
      rules.collect { case Rule(_, _, App(fun, _, _, List(App(constr, _, _, _))), _, True) => (fun.name.name, constr.name.name) } ==>
        List(("length", "Nil"), ("length", "Cons"))

    // annotations e as T of the expression are skipped when matching, e.g. [] as List<int>
    test("annotated"):
      val ints = Sort(Con("List", 1), List(Sort.int))
      val rules = List(rw(app(length, App(nil, Nil, list, Nil)), Zero.int))
      R(rules, app(length, As(App(nil, Nil, ints, Nil), ints))) ==> Zero.int

    // conditions are decided by the simplifier
    test("conditional"):
      val rule = rw(app(abs, x), x, Le.int(Zero.int, x))
      R(List(rule), app(abs, One.int)) ==> One.int
      R(List(rule), app(abs, a)) ==> app(abs, a)

    // variables that occur only in the condition are instantiated by matching it against the facts of the context,
    // the assumptions and the negated conclusions
    test("conditions bind variables"):
      val rule = Rule(Set(), Set(x, y), app(f, x), app(g, y), app(q, x, y))
      val ctx = Context.empty.assume(app(q, a, b)).withRules(List(rule))
      R(ctx, app(f, a)) ==> app(g, b)
      R(ctx, app(f, b)) ==> app(f, b)
      R(List(rule), app(f, a)) ==> app(f, a)

      val negated = Rule(Set(), Set(x, y), app(f, x), app(g, y), Not(app(q, x, y)))
      R(Context.empty.deny(app(q, a, b)).withRules(List(negated)), app(f, a)) ==> app(g, b)

    // closed conjuncts are decided first, conjuncts without any instantiated variable are not searched
    test("conditions closed and open"):
      val rule = Rule(Set(), Set(x, y), app(f, x), app(g, y), And(Le.int(Zero.int, x), app(q, x, y)))
      R(Context.empty.assume(app(q, a, b)).withRules(List(rule)), app(f, a)) ==> app(f, a)
      R(Context.empty.assume(app(q, a, b)).assume(Le.int(Zero.int, a)).withRules(List(rule)), app(f, a)) ==> app(g, b)

      val unrelated = Rule(Set(), Set(x, y), app(f, x), app(g, y), app(q, y, y))
      R(Context.empty.assume(app(q, b, b)).withRules(List(unrelated)), app(f, a)) ==> app(f, a)

    // variables of the rule match bound variables of the expression
    test("binders"):
      val rules = List(rw(app(f, app(g, x)), x))
      R(rules, All(List(a), Eq(app(f, app(g, a)), b))) ==> All(List(a), Eq(app(f, app(g, a)), b))
      R(rules, app(f, app(g, a))) ==> a

    // the number of steps is shared by all rewrites with the context
    test("nontermination"):
      val rules = List(rw(app(f, x), app(f, app(f, x))))
      val ctx = Context.empty.withRules(rules, steps = 10)
      val msg =
        try
          (0 to 10).foldLeft[Expr](app(f, a)): (expr, _) =>
            cuvee.simplify.Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, expr)
          "no error"
        catch case cuvee.Error(msg, _*) => msg
      msg ==> "rewriting does not terminate"

    // the variables of the right-hand side must occur in the left-hand side, other free variables are constants
    test("invalid rule"):
      val msg =
        try
          Rule.check(Rule(Set(), Set(x, y), app(f, x), y, True))
          "no error"
        catch case cuvee.Error(msg, _*) => msg
      msg ==> "variables of right hand side do not occur in left hand side or condition"
      Rule.check(Rule(Set(), Set(x), app(f, x), y, True))

    // constants of a rule are not instantiated
    test("constants"):
      val rules = List(Rule(Set(), Set(), app(f, a), b, True))
      R(rules, app(f, a)) ==> b
      R(rules, app(f, b)) ==> app(f, b)

    // sums modulo associativity, commutativity, and the neutral element 0
    test("sums"):
      val rules = List(rw(Plus.int(x, One.int), app(g, x)))
      R(rules, Plus.int(One.int, a)) ==> app(g, a)
      // at the top, x takes all other summands
      R(rules, Plus.int(List(a, One.int, b))) ==> app(g, Plus.int(a, b))
      R(rules, Plus.int(a, Plus.int(b, One.int))) ==> app(g, Plus.int(a, b))
      R(rules, Plus.int(Plus.int(a, b), One.int)) ==> app(g, Plus.int(a, b))
      R(rules, Minus.int(One.int, a)) ==> app(g, UMinus.int(a))
      R(rules, a) ==> a

    // a negated variable takes negative summands only, not the negation of others
    test("negations"):
      val rules = List(rw(app(f, UMinus.int(x)), app(g, x)))
      R(rules, app(f, UMinus.int(a))) ==> app(g, a)
      R(rules, app(f, Minus.int(UMinus.int(a), b))) ==> app(g, Plus.int(a, b))
      R(rules, app(f, Plus.int(a, One.int))) ==> app(f, Plus.int(a, One.int))

    test("differences"):
      val rules = List(rw(app(f, Minus.int(x, y)), app(g, y)))
      R(rules, app(f, Plus.int(a, UMinus.int(b)))) ==> app(g, b)
      R(rules, app(f, Minus.int(Minus.int(a, b), Zero.int))) ==> app(g, b)

    // comparisons modulo moving summands between the sides, where < on Int is <= with 1 added on the left
    test("comparisons"):
      val p = Fun("p", Nil, Fun.formals(Sort.int, Sort.int), Sort.bool)
      R(List(rw(Le.int(Plus.int(x, One.int), y), app(p, x, y))), Lt.int(a, b)) ==> app(p, a, b)
      R(List(rw(Lt.int(x, y), app(p, x, y))), Le.int(Plus.int(a, One.int), b)) ==> app(p, a, b)
      R(List(rw(Le.int(x, y), app(p, x, y))), Le.int(Minus.int(a, b), Zero.int)) ==> app(p, a, b)

    // on Real, the strictness must agree
    test("real comparisons"):
      val r = Var("r", Sort.real)
      val s = Var("s", Sort.real)
      val c = Var("c", Sort.real)
      val d = Var("d", Sort.real)
      val q = Fun("q", Nil, Fun.formals(Sort.real, Sort.real), Sort.bool)
      val rule = rw(Lt.real(r, s), App(q, List(r, s)))
      R(List(rule), Lt.real(c, d)) ==> App(q, List(c, d))
      R(List(rule), Le.real(c, d)) ==> Le.real(c, d)

    // a variable of the pattern may take the neutral element if the expression is a sum, where 0 is dropped
    test("neutral"):
      val rules = List(rw(app(f, Plus.int(x, y)), app(g, y)))
      R(rules, app(f, Plus.int(a, Zero.int))) ==> app(g, Zero.int)
      R(rules, app(f, a)) ==> app(f, a)

      // but only if there are fewer summands than variables, x + y matches a + b with x = a or x = b, not x = 0
      val ms = cuvee.simplify.Rewrite.matches(cuvee.Config.default, State.empty, Context.empty, Set(), Set(x, y), Set(), Plus.int(x, y), None, Map(), Set(), Plus.int(a, b), Subst.empty)
      ms.map(_.vars(x)) ==> List(a, b)

// the simplifier applies the rewrite rules of its context after each round of simplification
object SimplifyRules extends TestSuite:
  import Rewrite.rw
  import cuvee.simplify.{Context, Simplify}

  val a = Var("a", Sort.int)
  val x = Var("x", Sort.int)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)
  val g = Fun("g", Nil, Fun.formals(Sort.int), Sort.int)
  val abs = Fun("abs", Nil, Fun.formals(Sort.int), Sort.int)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  def simplify(rules: List[Rule], expr: Expr) =
    Simplify.simplify(cuvee.Config.default, State.empty, Context.pos.withRules(rules), expr)

  val tests = Tests:
    // the argument is simplified first, then the rule applies to the result
    test("after simplification"):
      val rules = List(rw(app(f, app(g, x)), x))
      simplify(rules, app(f, app(g, Plus.int(a, Zero.int)))) ==> a

    // the condition of the rule follows from the context
    test("conditional"):
      val rules = List(rw(app(abs, x), x, Le.int(Zero.int, x)))
      simplify(rules, Imp(Le.int(Zero.int, a), Eq(app(abs, a), a))) ==> True
      simplify(rules, Eq(app(abs, a), a)) ==> Eq(app(abs, a), a)

    // the results of rules are simplified further
    test("further"):
      val rules = List(rw(app(f, x), Plus.int(x, Minus.int(x, x))))
      simplify(rules, Eq(app(f, a), a)) ==> True
