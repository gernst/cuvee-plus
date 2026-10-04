package cuvee.test
package dafny

import utest._

import cuvee.core._
import cuvee.simplify.{Rule, Rewrite}

// verification by symbolic execution and trace equation systems:
// for programs without loops, the verdicts coincide with -verify,
// loops are summarized by trace equation systems, which the rewrite engine simplifies with lemmas
object TEQ extends TestSuite:
  import Verify.expected

  def loops(file: os.Path) =
    os.read(file).contains("while")

  // all subexpressions
  def subexprs(expr: Expr): List[Expr] =
    expr :: expr.subexprs.flatMap(subexprs)

  val tests = Tests:
    test("without loops"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filterNot(loops)
      do
        val first = os.read.lines(file).head
        Examples.errors("-teq", "-z3", file.toString) ==> expected(first)

    // break, continue, and return inside of loops: the loop is left by a path that ends by break or return,
    // in addition to the exit where the guard does not hold
    test("jumps"):
      for name <- List("break.dfy", "continue.dfy", "return.dfy", "invalid_break.dfy")
      do
        val file = Examples.root / "dafny" / "vcgen" / name
        val (cmds, errors) = Examples.output("-teq", "-print", "null", file.toString)
        errors ==> Nil
        assert(cmds.exists { case Assert(Goal, _, _, _) => true; case _ => false })

    // the counter i of sum.dfy is recognized by the lemma of example 2.3
    test("counter"):
      val file = Examples.root / "dafny" / "vcgen" / "sum.dfy"
      val (cmds, errors) = Examples.output("-teq", "-print", "null", file.toString)
      errors ==> Nil
      val List(Assert(Goal, _, phi, _)) = cmds: @unchecked

      // one trace for each of i and s, each of which occurs once, shared by the check of the body and the exit
      val traces = subexprs(phi).collect { case t: Trace => t }
      assert(traces.length == 2 && traces.distinct.length == 2)
      assert(subexprs(phi).exists(_.isInstanceOf[Invs]))

      val i = Var("i", Sort.int)
      val c = Var("c", Sort.int)
      val x = Var("x", Sort.int)
      val k = Var("k", Sort.int)
      val K = Var("K", Sort.trace(Sort.int))
      val butlast = App(Fun.trace.butlast, List(K))
      val rule = Rule(
        Trace(i, List(butlast), x, List(k), List(Upd(True, Plus.int(x, c)))),
        App(Fun.trace.counter, List(i, c, App(Fun.trace.steps, List(K))))
      )

      val phi_ = Rewrite(List(rule), phi)
      val counters = subexprs(phi_).collect { case app @ App(fun, _, _, List(Zero.int, One.int, _)) if fun == Fun.trace.counter => app }
      // the synthetic counter K = counter(0, 1, n) and the loop variable i = counter(0, 1, steps(K))
      assert(counters.exists { case App(_, _, _, List(_, _, App(fun, _, _, _))) => fun == Fun.trace.steps; case _ => false })
      assert(subexprs(phi_).collect { case t: Trace => t }.distinct.length == 1)
