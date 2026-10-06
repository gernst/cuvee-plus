package cuvee.test
package simplify

import utest._

import cuvee.Config
import cuvee.core._
import cuvee.simplify.{Ctx, Simplify}

// programs are simplified statement by statement, each helper normalizes its own constructor
object Programs extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val z = Var("z", Sort.int)
  val p = Var("p", Sort.bool)

  val inc = Assign(List(x), List(Plus.int(x, One.int)))
  val dec = Assign(List(x), List(Zero.int))

  def simplify(prog: Prog) =
    Simplify.simplify(Config.default, State.empty, Ctx.empty, prog)

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
    Simplify.simplify(Config.default, State.empty, Ctx.empty, expr)

  val tests = Tests:
    test("unused"):
      simplify(Maps(List(K, J), List(k, j), List(Upd(True, j)))) ==> Maps(List(J), List(j), List(Upd(True, j)))
      // the counter is kept
      simplify(Maps(List(C, J), List(k, j), List(Upd(True, j)))) ==> Maps(List(C, J), List(k, j), List(Upd(True, j)))
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
      val ctx = Ctx.empty.assume(List(Invs(List(J), List(l), Lt.int(Zero.int, l))), Nil)
      def simplify(expr: Expr) = Simplify.simplify(Config.default, State.empty, ctx, expr)
      simplify(Invs(List(K, J), List(k, j), Lt.int(Zero.int, j))) ==> True
      val upds = List(Upd(Lt.int(Zero.int, j), j), Upd(Le.int(j, Zero.int), Zero.int))
      simplify(Maps(List(J), List(j), upds)) ==> Maps(List(J), List(j), List(Upd(True, j)))
      // not for other dependencies
      val other = Invs(List(K), List(k), Lt.int(Zero.int, k))
      simplify(other) ==> other
