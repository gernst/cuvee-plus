package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.{Rule, Rewrite => R, Simplify, Ctx}

object Rewrite extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val a = Var("a", Sort.int)
  val b = Var("b", Sort.int)

  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)
  val g = Fun("g", Nil, Fun.formals(Sort.int), Sort.int)
  val abs = Fun("abs", Nil, Fun.formals(Sort.int), Sort.int)

  // polymorphic lists, length(cons(x, xs)) = length(xs) + 1
  val p = Param.a
  val list = Sort(Con("List", 1), List(p))
  val nil = Fun("nil", List(p), Nil, list)
  val cons = Fun("cons", List(p), Fun.formals(p, list), list)
  val length = Fun("length", List(p), Fun.formals(list), Sort.int)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  val tests = Tests:
    test("plain"):
      val rules = List(Rule(app(f, app(g, x)), x), Rule(Plus.int(x, Zero.int), x))
      R(rules, Plus.int(app(f, app(g, Plus.int(a, Zero.int))), Zero.int)) ==> a

    // the variables of a rule must be instantiated consistently
    test("nonlinear"):
      val rules = List(Rule(Minus.int(x, x), Zero.int))
      R(rules, Minus.int(a, a)) ==> Zero.int
      R(rules, Minus.int(a, b)) ==> Minus.int(a, b)

    // innermost first, the first rule that applies is used
    test("order"):
      val rules = List(Rule(app(f, x), app(g, x)), Rule(app(f, x), x))
      R(rules, app(f, app(f, a))) ==> app(g, app(g, a))

    // the type parameters are instantiated, here with Int
    test("polymorphic"):
      val xs = Var("xs", list)
      val rules = List(
        Rule(app(length, App(nil, Nil, list, Nil)), Zero.int),
        Rule(app(length, app(cons, Var("y", p), xs)), Plus.int(app(length, xs), One.int))
      )

      val ints = Sort(Con("List", 1), List(Sort.int))
      val nil_ = App(nil, Nil, ints, Nil)
      val expr = app(length, app(cons, a, app(cons, b, nil_)))
      R(rules, expr) ==> Plus.int(Plus.int(Zero.int, One.int), One.int)

    // conditions are decided by the simplifier
    test("conditional"):
      val rule = Rule(app(abs, x), x, Le.int(Zero.int, x))
      val holds = (phi: Expr) => Simplify.simplify(State.empty, Ctx.empty, phi) == True
      val rewrite = new R(List(rule), holds)
      rewrite(app(abs, One.int)) ==> One.int
      rewrite(app(abs, a)) ==> app(abs, a)

    // inside of binders
    test("binders"):
      val rules = List(Rule(app(f, app(g, x)), x))
      R(rules, All(List(a), Eq(app(f, app(g, a)), b))) ==> All(List(a), Eq(a, b))

    test("nontermination"):
      val rules = List(Rule(app(f, x), app(f, app(f, x))))
      val msg =
        try
          new R(rules, steps = 10)(app(f, a))
          "no error"
        catch case cuvee.Error(msg, _*) => msg
      msg ==> "rewriting does not terminate"

    test("invalid rule"):
      val msg =
        try
          Rule(app(f, x), y)
          "no error"
        catch case cuvee.Error(msg, _*) => msg
      msg ==> "variables of right hand side or condition do not occur in left hand side"

    // sums modulo associativity, commutativity, and the neutral element 0
    test("sums"):
      val rules = List(Rule(Plus.int(x, One.int), app(g, x)))
      R(rules, Plus.int(One.int, a)) ==> app(g, a)
      // innermost first: (a + 1) + b
      R(rules, Plus.int(List(a, One.int, b))) ==> Plus.int(app(g, a), b)
      R(rules, Plus.int(a, Plus.int(b, One.int))) ==> Plus.int(a, app(g, b))
      R(rules, Plus.int(Plus.int(a, b), One.int)) ==> app(g, Plus.int(a, b))
      R(rules, Minus.int(One.int, a)) ==> app(g, UMinus.int(a))
      R(rules, a) ==> a

    test("differences"):
      val rules = List(Rule(app(f, Minus.int(x, y)), app(g, y)))
      R(rules, app(f, Plus.int(a, UMinus.int(b)))) ==> app(g, b)
      R(rules, app(f, Minus.int(Minus.int(a, b), Zero.int))) ==> app(g, b)

    // a variable of the pattern may take the neutral element if the expression is a sum, where 0 is dropped
    test("neutral"):
      val rules = List(Rule(app(f, Plus.int(x, y)), app(g, y)))
      R(rules, app(f, Plus.int(a, Zero.int))) ==> app(g, Zero.int)
      R(rules, app(f, a)) ==> app(f, a)
