package cuvee.test
package dafny

import utest._

import cuvee.core._
import cuvee.simplify.{Rule, Rewrite}

// verification by symbolic execution and trace equation systems:
// for programs without loops, the verdicts coincide with -verify,
// loops are summarized by trace equation systems, which the rewrite engine simplifies with lemmas
object TEQ extends TestSuite:
  // a rule whose variables are the free variables of its left-hand side
  def rw(lhs: Expr, rhs: Expr, cond: Expr = True) =
    Rule(lhs, rhs, cond, lhs.free.toList)

  import Verify.expected

  def loops(file: os.Path) =
    os.read(file).contains("while")

  // all subexpressions
  def subexprs(expr: Expr): List[Expr] =
    val inner = List.newBuilder[Expr]
    expr.map: arg =>
      inner ++= subexprs(arg)
      arg
    expr :: inner.result()

  val tests = Tests:
    // the goals are passed to z3 without the lemma database, whose functions on traces z3 does not support
    test("without loops"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filterNot(loops)
      do
        val first = os.read.lines(file).head
        val (cmds, errors) = Examples.output("-teq", "-print", "null", file.toString)
        errors ==> Nil
        val goals = os.temp(cuvee.smtlib.Printer.lines(cmds.filterNot(cuvee.verify.TEQ.lemmas.contains)).mkString("\n"), suffix = ".smt2")
        Examples.errors("-z3", goals.toString) ==> expected(first)

    // the lemma database is injected at the beginning, whose counter lemma rewrites the trace of i in sum.dfy,
    // and whose lemma on sums rewrites that of s
    test("lemmas"):
      val sum = Examples.root / "dafny" / "vcgen" / "sum.dfy"
      val (cmds, errors) = Examples.output("-teq", "-simplify", "-print", "null", sum.toString)
      errors ==> Nil
      assert(cmds.exists { case DeclareFun(fun, _) => fun == Fun.trace.counter; case _ => false })
      val List(phi) = cmds.collect { case Assert(Goal, _, phi, _) => phi }: @unchecked
      assert(subexprs(phi).collect { case t: Trace => t }.isEmpty)
      assert(subexprs(phi).exists { case App(fun, _, _, _) => fun.name.name == "sums"; case _ => false })

      // also without loops, once at the beginning
      val abs = Examples.root / "dafny" / "vcgen" / "abs.dfy"
      val (cmds_, _) = Examples.output("-teq", "-print", "null", abs.toString)
      cmds_.take(cuvee.verify.TEQ.lemmas.length) ==> cuvee.verify.TEQ.lemmas
      cmds_.count(cuvee.verify.TEQ.lemmas.contains) ==> cuvee.verify.TEQ.lemmas.length

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
      val List(phi) = cmds.collect { case Assert(Goal, _, phi, _) => phi }: @unchecked

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
      val rule = rw(
        Trace(i, List(butlast), x, List(k), List(Upd(True, Plus.int(x, c)))),
        App(Fun.trace.counter, List(i, c, App(Fun.trace.steps, List(K))))
      )

      val phi_ = Rewrite(List(rule), phi)
      val counters = subexprs(phi_).collect { case app @ App(fun, _, _, List(Zero.int, One.int, _)) if fun == Fun.trace.counter => app }
      // the synthetic counter K = counter(0, 1, n) and the loop variable i = counter(0, 1, steps(K))
      assert(counters.exists { case App(_, _, _, List(_, _, App(fun, _, _, _))) => fun == Fun.trace.steps; case _ => false })
      assert(subexprs(phi_).collect { case t: Trace => t }.distinct.length == 1)

    // a variable that is increased where the values are equal to e counts the occurrences of e,
    // also on values of other types than bool, and on booleans whose guards are the values themselves
    test("counts"):
      val rules = cuvee.simplify.Simplify.rules(cuvee.verify.TEQ.lemmas)
      val counts = cuvee.verify.TEQ.lemmas.collectFirst { case DeclareFun(fun, _) if fun.name.name == "counts" => fun }.get
      val x = Var("x", Sort.int)
      val y = Var("y", Sort.int)
      val e = Var("e", Sort.real)
      val v = Var("v", Sort.real)
      val vs = Var("vs", Sort.seq(Sort.real))
      val b = Var("b", Sort.bool)
      val bs = Var("bs", Sort.seq(Sort.bool))

      val trues = Trace(x, List(bs), y, List(b), List(Upd(b, Plus.int(y, One.int)), Upd(Not(b), y)))
      Rewrite(rules, trues) ==> App(counts, List(x, True, bs))

      val falses = Trace(x, List(bs), y, List(b), List(Upd(Not(b), Plus.int(y, One.int)), Upd(b, y)))
      Rewrite(rules, falses) ==> App(counts, List(x, False, bs))

      val occurrences = Trace(x, List(vs), y, List(v), List(Upd(Eq(v, e), Plus.int(y, One.int)), Upd(Not(Eq(v, e)), y)))
      Rewrite(rules, occurrences) ==> App(counts, List(x, e, vs))
