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
      R(List(rule), app(abs, One.int)) ==> One.int
      R(List(rule), app(abs, a)) ==> app(abs, a)

    // inside of binders
    test("binders"):
      val rules = List(Rule(app(f, app(g, x)), x))
      R(rules, All(List(a), Eq(app(f, app(g, a)), b))) ==> All(List(a), Eq(a, b))

    test("nontermination"):
      val rules = List(Rule(app(f, x), app(f, app(f, x))))
      val msg =
        try
          R.rewrite(cuvee.Config.default, State.empty, Ctx.empty.withRules(rules, steps = 10), app(f, a))
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

    // comparisons modulo moving summands between the sides, where < on Int is <= with 1 added on the left
    test("comparisons"):
      val p = Fun("p", Nil, Fun.formals(Sort.int, Sort.int), Sort.bool)
      R(List(Rule(Le.int(Plus.int(x, One.int), y), app(p, x, y))), Lt.int(a, b)) ==> app(p, a, b)
      R(List(Rule(Lt.int(x, y), app(p, x, y))), Le.int(Plus.int(a, One.int), b)) ==> app(p, a, b)
      R(List(Rule(Le.int(x, y), app(p, x, y))), Le.int(Minus.int(a, b), Zero.int)) ==> app(p, a, b)
      R(List(Rule(Lt.int(x, y), app(p, x, y))), Gt.int(b, a)) ==> app(p, a, b)

    // on Real, the strictness must agree
    test("real comparisons"):
      val r = Var("r", Sort.real)
      val s = Var("s", Sort.real)
      val c = Var("c", Sort.real)
      val d = Var("d", Sort.real)
      val q = Fun("q", Nil, Fun.formals(Sort.real, Sort.real), Sort.bool)
      val rule = Rule(Lt.real(r, s), App(q, List(r, s)))
      R(List(rule), Lt.real(c, d)) ==> App(q, List(c, d))
      R(List(rule), Le.real(c, d)) ==> Le.real(c, d)

    // a variable of the pattern may take the neutral element if the expression is a sum, where 0 is dropped
    test("neutral"):
      val rules = List(Rule(app(f, Plus.int(x, y)), app(g, y)))
      R(rules, app(f, Plus.int(a, Zero.int))) ==> app(g, Zero.int)
      R(rules, app(f, a)) ==> app(f, a)

// the simplifier applies the rewrite rules of its context after each round of simplification
object SimplifyRules extends TestSuite:
  import cuvee.simplify.{Ctx, Simplify}

  val a = Var("a", Sort.int)
  val x = Var("x", Sort.int)
  val f = Fun("f", Nil, Fun.formals(Sort.int), Sort.int)
  val g = Fun("g", Nil, Fun.formals(Sort.int), Sort.int)
  val abs = Fun("abs", Nil, Fun.formals(Sort.int), Sort.int)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  def simplify(rules: List[Rule], expr: Expr) =
    Simplify.simplify(cuvee.Config.default, State.empty, Ctx.pos.withRules(rules), expr)

  val tests = Tests:
    // the argument is simplified first, then the rule applies to the result
    test("after simplification"):
      val rules = List(Rule(app(f, app(g, x)), x))
      simplify(rules, app(f, app(g, Plus.int(a, Zero.int)))) ==> a

    // the condition of the rule follows from the context
    test("conditional"):
      val rules = List(Rule(app(abs, x), x, Le.int(Zero.int, x)))
      simplify(rules, Imp(Le.int(Zero.int, a), Eq(app(abs, a), a))) ==> True
      simplify(rules, Eq(app(abs, a), a)) ==> Eq(app(abs, a), a)

    // the results of rules are simplified further
    test("further"):
      val rules = List(Rule(app(f, x), Plus.int(x, Minus.int(x, x))))
      simplify(rules, Eq(app(f, a), a)) ==> True

// rewrite rules are assertions and lemmas with the attribute :rw in Dafny, Boogie, and SMT-LIB (see examples/simplify)
object Rules extends TestSuite:
  def simplify(text: String, suffix: String) =
    val file = os.temp(text, suffix = suffix)
    Examples.output("-simplify", file.toString)

  val tests = Tests:
    test("dafny"):
      val (cmds, errors) = simplify("""
        function f(x: int): int
        function g(x: int): int
        predicate p(x: int)
        axiom {:rw} forall x: int :: f(g(x)) == x
        lemma {:rw} forall x: int :: 0 <= x ==> p(x)
        function h(a: int): bool { f(g(a)) == a && p(1) }
      """, ".dfy")
      errors ==> Nil
      cuvee.dafny.Printer.lines(cmds.last) ==> List("function h(a: int): bool {", "  true", "}", "")

    test("boogie"):
      val (cmds, errors) = simplify("""
        function f(x: int): int;
        function g(x: int): int;
        axiom {:rw} (forall x: int :: f(g(x)) == x);
        lemma {:rw} (forall x: int :: !(f(x) < 0));
        function h(a: int): bool { f(g(a)) == a && !(f(a) < 0) }
      """, ".bpl")
      errors ==> Nil
      cuvee.boogie.Printer.lines(cmds.last) ==> List("function h(a: int): bool { true }", "")

    // the rules are printed with their attribute, which parses back
    test("printing"):
      val (cmds, errors) = simplify("function f(x: int): int axiom {:rw} forall x: int :: f(f(x)) == x", ".dfy")
      errors ==> Nil
      cuvee.dafny.Printer.lines(cmds.last) ==> List("axiom {:rw} forall x: int :: f(f(x)) == x", "")

    test("invalid"):
      val (_, errors) = simplify("predicate p(x: int) axiom {:rw} forall x: int :: p(x) && p(x + 1)", ".dfy")
      errors ==> List("rewrite rule is not an equation, an equivalence, a negation, or a boolean atom")
