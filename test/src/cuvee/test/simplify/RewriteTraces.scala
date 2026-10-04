package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.{Rule, Rewrite => R}

// patterns with the combinators trace, map, and all, as in the examples of Trace Equation Systems
object RewriteTraces extends TestSuite:
  val int = Sort.int
  val ints = Sort.seq(int)
  val trace = Sort.trace(int)
  val array = Sort.array(int, int)

  // ⌊X⌋, the trace without its last element
  val butlast = Fun("butlast", Nil, Fun.formals(trace), ints)
  val counter = Fun("counter", Nil, Fun.formals(int, int, int), trace)
  val steps = Fun("steps", Nil, Fun.formals(ints), int)
  val sums = Fun("sums", Nil, Fun.formals(int, ints), trace)
  val selects = Fun("selects", Nil, Fun.formals(array, ints), ints)

  def app(fun: Fun, args: Expr*) = App(fun, args.toList)

  // variables of the rules
  val i = Var("i", int)
  val c = Var("c", int)
  val x = Var("x", int)
  val v = Var("v", int)
  val k = Var("k", int)
  val a = Var("a", array)
  val K = Var("K", trace)
  val V = Var("V", ints)
  val Ks = Var("Ks", ints)

  // variables of the expressions
  val s = Var("s", int)
  val j = Var("j", int)
  val arr = Var("arr", array)
  val J = Var("J", trace)
  val n = Var("n", int)

  // trace(i, for ⌊K⌋ do i, k ↦ i + c) = counter(i, c, steps(⌊K⌋))
  val counterRule =
    Rule(Trace(i, List(app(butlast, K)), x, List(k), List((True, Plus.int(x, c)))), app(counter, i, c, app(steps, app(butlast, K))))

  // trace(i, for V do x, v ↦ x + v) = sums(i, V)
  val sumsRule =
    Rule(Trace(i, List(V), x, List(v), List((True, Plus.int(x, v)))), app(sums, i, V))

  // map(for K yield k ↦ a[k]) = selects(a, K)
  val selectsRule =
    Rule(Maps(List(Ks), List(k), List((True, Select(a, k)))), app(selects, a, Ks))

  val tests = Tests:
    // example 2.3, the counter is matched modulo commutativity
    test("counter"):
      val expr = Trace(Zero.int, List(app(butlast, J)), s, List(j), List((True, Plus.int(One.int, s))))
      R(List(counterRule), expr) ==> app(counter, Zero.int, One.int, app(steps, app(butlast, J)))

    // example 2.6, the dependency V is instantiated by a map over the dependencies of the expression
    test("sums"):
      val expr = Trace(Zero.int, List(app(butlast, J)), s, List(j), List((True, Plus.int(s, Select(arr, j)))))
      val values = Maps(List(app(butlast, J)), List(j), List((True, Select(arr, j))))
      R(List(sumsRule), expr) ==> app(sums, Zero.int, values)

    // ... which is then recognized as selects, example 6.2
    test("sums of selects"):
      val expr = Trace(Zero.int, List(app(butlast, J)), s, List(j), List((True, Plus.int(s, Select(arr, j)))))
      R(List(sumsRule, selectsRule), expr) ==> app(sums, Zero.int, app(selects, arr, app(butlast, J)))

    // a bound variable that is the value directly yields the dependency itself
    test("dependency"):
      val W = Var("W", ints)
      val w = Var("w", int)
      val expr = Trace(Zero.int, List(W), s, List(w), List((True, Plus.int(w, s))))
      R(List(sumsRule), expr) ==> app(sums, Zero.int, W)

    // the value must not depend on the accumulator
    test("accumulator"):
      val expr = Trace(Zero.int, List(app(butlast, J)), s, List(j), List((True, Plus.int(s, Times.int(s, j)))))
      R(List(sumsRule), expr) ==> expr

    // every case of the update of the expression is covered by the single case of the pattern
    test("cases"):
      val expr = Trace(Zero.int, List(app(butlast, J)), s, List(j), List(
        (Lt.int(j, n), Plus.int(s, One.int)),
        (Not(Lt.int(j, n)), Plus.int(s, One.int))
      ))
      R(List(counterRule), expr) ==> app(counter, Zero.int, One.int, app(steps, app(butlast, J)))

    // different increments in the cases are not a counter
    test("different cases"):
      val expr = Trace(Zero.int, List(app(butlast, J)), s, List(j), List(
        (Lt.int(j, n), Plus.int(s, One.int)),
        (Not(Lt.int(j, n)), Plus.int(s, Plus.int(One.int, One.int)))
      ))
      R(List(counterRule), expr) ==> expr

    // all(for ⌊K⌋ check k ↦ k < len) with the bound variable related to that of the expression
    test("all"):
      val len = Var("len", int)
      val rule = Rule(Invs(List(app(butlast, K)), List(k), Lt.int(k, len)), Le.int(app(steps, app(butlast, K)), len))
      val expr = Invs(List(app(butlast, J)), List(j), Lt.int(j, n))
      R(List(rule), expr) ==> Le.int(app(steps, app(butlast, J)), n)

    // the variables of the rule must not capture the bound variables of the expression
    test("capture"):
      val rule = Rule(Invs(List(app(butlast, K)), List(k), Lt.int(c, k)), True)
      val expr = Invs(List(app(butlast, J)), List(j), Lt.int(j, j))
      R(List(rule), expr) ==> expr
