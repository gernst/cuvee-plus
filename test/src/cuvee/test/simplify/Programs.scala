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
  val skip = Block(Nil, Nil)

  def simplify(prog: Prog) =
    Simplify.simplify(Config.default, State.empty, Ctx.empty, prog)

  val tests = Tests:
    // assignments of variables to themselves and trivial specifications have no effect
    test("skip"):
      simplify(Assign(List(x, y), List(x, Zero.int))) ==> Assign(List(y), List(Zero.int))
      simplify(Assign(List(x), List(x))) ==> skip
      simplify(Spec(Nil, True, True)) ==> skip

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
      simplify(While(False, inc, Attrs.empty)) ==> skip

    test("choice"):
      simplify(Choice(List(inc, Choice(List(dec, inc))))) ==> Choice(List(inc, dec))
      simplify(Choice(List(inc, inc))) ==> inc
