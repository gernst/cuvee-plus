package cuvee.test
package simplify

import utest._

import cuvee.Config
import cuvee.core._
import cuvee.simplify.{Context, Simplify}

// programs are simplified statement by statement, each helper normalizes its own constructor
object Programs extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val p = Var("p", Sort.bool)

  val inc = Assign(List(x), List(Plus.int(x, One.int)))
  val dec = Assign(List(x), List(Zero.int))

  def simplify(prog: Prog) =
    Simplify.simplify(Config.default, State.empty, Context.empty, prog)

  val tests = Tests:
    // assignments of variables to themselves and trivial specifications have no effect
    test("skip"):
      simplify(Assign(List(x, y), List(x, Zero.int))) ==> Assign(List(y), List(Zero.int))
      simplify(Assign(List(x), List(x))) ==> Skip
      simplify(Spec(Nil, True, True)) ==> Skip

    // nested blocks are merged, also with locals, unless these capture variables of the other statements
    test("blocks"):
      simplify(Block(Nil, List(inc, Block(Nil, List(dec, Assign(List(y), List(y))))))) ==> Block(Nil, List(inc, dec))
      simplify(Block(Nil, List(Block(Nil, List(inc))))) ==> inc
      simplify(Block(Nil, List(Block(List(z), List(Assign(List(z), List(x)), Assign(List(x), List(z))))))) ==>
        Block(List(z), List(Assign(List(z), List(x)), Assign(List(x), List(z))))
      val capture = Block(Nil, List(Block(List(z), List(Assign(List(z), List(x)))), Assign(List(x), List(z))))
      simplify(capture) ==> capture
      // unused locals are dropped
      simplify(Block(List(z), List(inc, dec))) ==> Block(Nil, List(inc, dec))

    // statements after a jump are not reached
    test("jumps"):
      simplify(Block(Nil, List(inc, Break, dec))) ==> Block(Nil, List(inc, Break))

    // constant tests select a branch, equal branches make the test irrelevant, negated tests swap the branches
    test("if"):
      simplify(If(True, inc, dec)) ==> inc
      simplify(If(Not(True), inc, dec)) ==> dec
      simplify(If(p, inc, inc)) ==> inc
      simplify(If(Not(p), inc, dec)) ==> If(p, dec, inc)

    test("while"):
      simplify(While(False, inc, Attrs.empty)) ==> Skip

    test("choice"):
      simplify(Choice(List(inc, Choice(List(dec, inc))))) ==> Choice(List(inc, dec))
      simplify(Choice(List(inc, inc))) ==> inc

// the dependencies of combinators: unused ones are dropped, except counters, equal ones are collapsed
object Dependencies extends TestSuite:
  val n = Var("n", Sort.int)
  val j = Var("j", Sort.int)
  val k = Var("k", Sort.int)
  val l = Var("l", Sort.int)
  val J = Var("J", Sort.seq(Sort.int))
  val K = Var("K", Sort.seq(Sort.int))
  val C = Butlast(Counter(Zero.int, One.int, n))

  def simplify(expr: Expr) =
    Simplify.simplify(Config.default, State.empty, Context.empty, expr)

  val tests = Tests:
    test("unused"):
      simplify(Maps(List(K, J), List(k, j), j)) ==> Maps(List(J), List(j), j)
      // the counter is kept
      simplify(Maps(List(C, J), List(k, j), j)) ==> Maps(List(C, J), List(k, j), j)
      // the first dependency is kept if none remains
      simplify(Invs(List(K, J), List(k, j), Lt.int(Zero.int, n))) ==> Invs(List(K), List(k), Lt.int(Zero.int, n))

    test("duplicates"):
      val Invs(deps, List(j_), body) = simplify(Invs(List(J, J), List(j, l), Lt.int(n, Plus.int(j, l)))): @unchecked
      deps ==> List(J)
      body.free ==> Set(n, j_)

    // invariants distribute over conjunctions, each part keeps the dependencies that it uses
    test("conjunctions"):
      val phi = Invs(List(K, J), List(k, j), And(Lt.int(Zero.int, k), Lt.int(Zero.int, j)))
      simplify(phi) ==> And(Invs(List(K), List(k), Lt.int(Zero.int, k)), Invs(List(J), List(j), Lt.int(Zero.int, j)))

    // the invariants of the context over some of the dependencies hold in the bodies and updates
    test("invariants"):
      val ctx = Context.empty.assume(List(Invs(List(J), List(l), Lt.int(Zero.int, l))), Nil)
      def simplify(expr: Expr) = Simplify.simplify(Config.default, State.empty, ctx, expr)
      simplify(Invs(List(K, J), List(k, j), Lt.int(Zero.int, j))) ==> True
      val upds = Eps(List(Upd(Lt.int(Zero.int, j), j), Upd(Le.int(j, Zero.int), Zero.int)))
      simplify(Maps(List(J), List(j), upds)) ==> Maps(List(J), List(j), j)
      // not for other dependencies
      val other = Invs(List(K), List(k), Lt.int(Zero.int, k))
      simplify(other) ==> other

    // the invariants that mention the combinator itself hold in its update: in X == trace(...), ⌊X⌋ is the accumulator,
    // and in Y == maps(...), Y is the update, e.g. the test of a loop lo < hi in the trace of lo
    test("invariants of the defined combinator"):
      val X = Var("X", Sort.trace(Sort.int))
      val Y = Var("Y", Sort.seq(Sort.int))
      val x = Var("x", Sort.int)
      val y = Var("y", Sort.int)
      val loop = Invs(List(Butlast(X), J), List(x, j), Lt.int(x, j))
      val ctx = Context.empty.assume(List(loop), Nil)
      def simplify(expr: Expr) = Simplify.simplify(Config.default, State.empty, ctx, expr)

      val update = Ite(Lt.int(x, j), One.int, Zero.int)
      val trace = Trace(Zero.int, List(J), x, List(j), update)
      simplify(Eq(X, trace)) ==> Eq(X, Trace(Zero.int, List(J), x, List(j), One.int))
      // not without the equation
      simplify(trace) ==> trace

      val positive = Invs(List(Y, J), List(y, j), Lt.int(Zero.int, j))
      val ctx_ = Context.empty.assume(List(positive), Nil)
      val abs = Maps(List(J), List(j), Ite(Lt.int(Zero.int, j), j, UMinus.int(j)))
      Simplify.simplify(Config.default, State.empty, ctx_, Eq(Y, abs)) ==> Eq(Y, Maps(List(J), List(j), j))

    // the iterations of a loop, counted by the first dependency, are 0 <= k < n,
    // and the other dependencies have their values in iteration k
    test("iterations"):
      simplify(Invs(List(C), List(k), Le.int(Zero.int, k))) ==> True
      simplify(Invs(List(C), List(k), Lt.int(k, n))) ==> True
      simplify(Invs(List(C, J), List(k, j), Eq(j, Earlier(k, J)))) ==> True
      val upds = Eps(List(Upd(Lt.int(k, n), j), Upd(Le.int(n, k), Zero.int)))
      simplify(Maps(List(C, J), List(k, j), upds)) ==> Maps(List(C, J), List(k, j), j)
      // also for a variable that denotes the counter by an assumption
      val I = Var("I", Sort.trace(Sort.int))
      val ctx = Context.empty.assume(List(Eq(I, Counter(Zero.int, One.int, n))), Nil)
      Simplify.simplify(Config.default, State.empty, ctx, Invs(List(Butlast(I)), List(k), Lt.int(k, n))) ==> True
      // not for other dependencies
      val other = Invs(List(J), List(j), Le.int(Zero.int, j))
      simplify(other) ==> other

    // the result of a case assumes that the guards of the other cases are false, not so its guard
    test("other guards"):
      val b = Var("b", Sort.bool)
      val c = Var("c", Sort.bool)
      val upds = Eps(List(Upd(b, Ite(c, One.int, j)), Upd(c, Ite(b, Zero.int, Plus.int(j, One.int)))))
      simplify(Maps(List(J), List(j), upds)) ==> Maps(List(J), List(j), Eps(List(Upd(b, j), Upd(c, Plus.int(j, One.int)))))
