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
      for file <- Examples.find(os.sub / "vcgen", "dfy").filterNot(loops)
      do
        val first = os.read.lines(file).head
        Examples.errors("-teq", "-z3", file.toString) ==> expected(first)

    // the counter i of sum.dfy is recognized by the lemma of example 2.3
    test("counter"):
      val file = Examples.root / "vcgen" / "sum.dfy"
      val (cmds, errors) = Examples.output("-teq", "-print", "null", file.toString)
      errors ==> Nil
      val List(Assert(Goal, _, phi, _)) = cmds: @unchecked

      // the system occurs in the check of the body and at the exit
      val traces = subexprs(phi).collect { case t: Trace => t }.distinct
      assert(traces.length == 2)
      assert(subexprs(phi).exists(_.isInstanceOf[Invs]))

      val i = Var("i", Sort.int)
      val c = Var("c", Sort.int)
      val x = Var("x", Sort.int)
      val k = Var("k", Sort.int)
      val K = Var("K", Sort.trace(Sort.int))
      val butlast = App(Fun.trace.butlast, List(K))
      val rule = Rule(
        Trace(i, List(butlast), x, List(k), List((True, Plus.int(x, c)))),
        App(Fun.trace.counter, List(i, c, App(Fun.trace.steps, List(K))))
      )

      val phi_ = Rewrite(List(rule), phi)
      val counters = subexprs(phi_).collect { case app @ App(fun, _, _, List(Zero.int, One.int, _)) if fun == Fun.trace.counter => app }
      // the synthetic counter K = counter(0, 1, n) and the loop variable i = counter(0, 1, steps(K))
      assert(counters.exists { case App(_, _, _, List(_, _, App(fun, _, _, _))) => fun == Fun.trace.steps; case _ => false })
      assert(subexprs(phi_).collect { case t: Trace => t }.distinct.length == 1)
