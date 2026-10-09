package cuvee.test
package dafny

import utest._

import cuvee.core._
import cuvee.simplify.Rule
import cuvee.simplify.Rewrite

// verification by symbolic execution and trace equation systems:
// for programs without loops, the verdicts coincide with -verify,
// loops are summarized by trace equation systems, which the rewrite engine simplifies with lemmas;
// the programs whose goals vanish are in examples/c/teq, examples/dafny/teq, and examples/dafny/parsing/teq_*.dfy
object TEQ extends TestSuite:
  // a rule whose type parameters and variables are the free ones of its left-hand side
  def rw(lhs: Expr, rhs: Expr, cond: Expr = True) =
    Rule(lhs.params, lhs.free, lhs, rhs, cond)

  def loops(file: os.Path) =
    os.read(file).contains("while")

  // all subexpressions
  def subexprs(expr: Expr): List[Expr] =
    val inner = List.newBuilder[Expr]
    expr.map: arg =>
      inner ++= subexprs(arg)
      arg
    expr :: inner.result()

  val contracts = "calls of procedures with a contract are not supported"

  val tests = Tests:
    // goals are generated without errors (z3 is never run on them);
    // examples that call methods with a contract are rejected, since calls are inlined (see "calls with contract")
    test("without loops"):
      for file <- Examples.find(os.sub / "dafny" / "vcgen", "dfy").filterNot(loops)
      do
        val (cmds, errors) = Examples.output("-teq", "-print", "null", file.toString)
        if errors != List(contracts)
        then
          errors ==> Nil
          assert(cmds.exists { case Assert(Goal, _, _, _) => true; case _ => false })

    // the lemma database is injected at the beginning, whose counter lemma rewrites the trace of i in sum.dfy;
    // that of s, which the lemma on sums rewrites, is unused, its equation vanishes by the one-point rule;
    // the invariant over the counter is rewritten as well, such that only arithmetic remains
    test("lemmas"):
      val sum = Examples.root / "dafny" / "vcgen" / "sum.dfy"
      val (cmds, errors) = Examples.stream("-teq", "-simplify", "-print", "null", sum.toString)
      errors ==> Nil
      assert(cmds.exists { case DeclareFun(fun, _) => fun == Fun.trace.counter; case _ => false })
      val List(phi) = cmds.collect { case Assert(Goal, _, phi, _) => phi }: @unchecked
      assert(subexprs(phi).collect { case t: Trace => t }.isEmpty)
      assert(!subexprs(phi).exists { case App(fun, _, _, _) => fun == Fun.trace.counter; case _ => false })
      assert(!subexprs(phi).exists { case App(fun, _, _, _) => fun.name.name == "sums"; case _ => false })

      // also without loops, once at the beginning
      val abs = Examples.root / "dafny" / "vcgen" / "abs.dfy"
      val (cmds_, _) = Examples.stream("-teq", "-print", "null", abs.toString)
      val prelude = Examples.prelude("-teq", "-print", "null", abs.toString)
      cmds_.filterNot(prelude.contains).take(cuvee.verify.TEQ.lemmas.length) ==> cuvee.verify.TEQ.lemmas
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
      val n = Var("n", Sort.int)
      val x = Var("x", Sort.int)
      val k = Var("k", Sort.int)
      val rule = rw(
        Trace(i, List(Butlast(Counter(Zero.int, One.int, n))), x, List(k), Plus.int(x, c)),
        Counter(i, c, n)
      )

      // the synthetic counter K == counter(0, 1, n) is followed from the premises (see Context.↑),
      // the trace of the loop variable i becomes counter(0, 1, n), only that of s remains
      val phi_ = cuvee.simplify.Simplify(cuvee.Config.default, State.empty, cuvee.simplify.Context.pos.withRules(List(rule)), phi)
      assert(subexprs(phi_).collect { case t: Trace => t }.distinct.length == 1)

    // an update of a visited key replaces its contribution to the count, and the prefix counts are counts of prefixes;
    // the conditions are decided by the assumptions of the context
    test("count"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      def fun(name: String) = cuvee.verify.TEQ.lemmas.collectFirst { case DeclareFun(fun, _) if fun.name.name == name => fun; case DefineFun(fun, _, _) if fun.name.name == name => fun }.get
      def app(name: String, args: Expr*) = App(fun(name), args.toList)
      def has(expr: Expr, name: String) = subexprs(expr).exists { case App(f, _, _, _) => f.name.name == name; case _ => false }

      val a = Var("a", Sort.array(Sort.int, Sort.int))
      val k = Var("k", Sort.int)
      val w = Var("w", Sort.int)
      val e = Var("e", Sort.int)
      val j = Var("j", Sort.int)
      val x = Var("x", Sort.int)
      val keys = Var("keys", Sort.seq(Sort.int))

      val ctx = cuvee.simplify.Context.empty.assume(app("distincts", keys)).withRules(rules)
      val updated = Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, app("count", e, app("selects", Store(a, k, w), keys)))
      assert(subexprs(updated).contains(app("count", e, app("selects", a, keys))))
      assert(!subexprs(updated).exists { case Store(_, _, _) => true; case _ => false })

      val bounds = cuvee.simplify.Context.empty.assume(Le.int(Zero.int, j)).withRules(rules)
      val earlier = Rewrite.rewrite(cuvee.Config.default, State.empty, bounds, app("earlier", j, Butlast(app("counts", x, e, keys))))
      assert(subexprs(earlier).contains(app("count", e, app("prefix", j, keys))))
      assert(!has(earlier, "counts"))

    // the invariant of a loop condition i < 1024 over a counter is rewritten by the lemma for k < m,
    // which is m - k - 1 on Int, whereas the constant of 1023 - i is folded,
    // also with a second dependency whose bound variable is unused, and with the counter defined in the context
    test("invs with literal bound"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      val n = Var("n", Sort.int)
      val trace = Sort(Con("Trace", 1), List(Sort.int))
      val I = Var("I", trace)
      val K = Var("K", trace)
      val i = Var("i", Sort.int)
      val k = Var("k", Sort.int)
      val bound = Lit(BigInt(1024), Sort.int)
      val counter = Counter(Zero.int, One.int, n)
      val ctx = cuvee.simplify.Context.empty.assume(Le.int(Zero.int, n)).assume(Eq(I, counter)).assume(Eq(K, counter)).withRules(rules)

      for inv <- List(
          Invs(List(Butlast(counter)), List(i), Lt.int(i, bound)),
          Invs(List(Butlast(I)), List(i), Lt.int(i, bound)),
          Invs(List(Butlast(K), Butlast(I)), List(k, i), Lt.int(i, bound)))
      do
        val inv_ = Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, inv)
        assert(!subexprs(inv_).exists(_.isInstanceOf[Invs]))

    // calls are inlined, which rejects callees with a contract
    test("calls with contract"):
      val file = Examples.root / "dafny" / "vcgen" / "call.dfy"
      val (_, errors) = Examples.output("-teq", "-print", "null", file.toString)
      errors ==> List(contracts)

    // a loop that assigns a constant: the dependency of the lemma whose bound variable the update does not use
    // is instantiated by a dependency of the expression, here the counter defined in the context
    test("constant updates"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      val n = Var("n", Sort.int)
      val trace = Sort(Con("Trace", 1), List(Sort.int))
      val K = Var("K", trace)
      val X = Var("X", trace)
      val x = Var("x", Sort.int)
      val k = Var("k", Sort.int)
      val loop = Trace(One.int, List(Butlast(K)), x, List(k), Zero.int)
      val ctx = cuvee.simplify.Context.empty.assume(Le.int(Zero.int, n)).assume(Eq(K, Counter(Zero.int, One.int, n))).assume(Eq(X, loop)).withRules(rules)
      Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, Current(X)) ==> Ite(Eq(n, Zero.int), One.int, Zero.int)
