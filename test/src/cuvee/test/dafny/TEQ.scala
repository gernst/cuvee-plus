package cuvee.test
package dafny

import utest._

import cuvee.core._
import cuvee.prove.Rule
import cuvee.prove.Rewrite

// verification by symbolic execution and trace equation systems:
// for programs without loops, the verdicts coincide with -vcgen (global variables, old, and calls are in
// examples/dafny/teq/globals_calls.dfy), loops are summarized by trace equation systems, which the rewrite engine simplifies with lemmas;
// the programs whose goals vanish are in examples/c/teq, examples/dafny/teq, and examples/dafny/parsing/teq_*.dfy
object TEQ extends TestSuite:
  // a rule whose type parameters and variables are the free ones of its left-hand side
  def rw(lhs: Expr, rhs: Expr, cond: Expr = True) =
    Rule(lhs.params, lhs.free, lhs, rhs, cond)

  // all subexpressions
  def subexprs(expr: Expr): List[Expr] =
    val inner = List.newBuilder[Expr]
    expr.map: arg =>
      inner ++= subexprs(arg)
      arg
    expr :: inner.result()

  // the lemma database with the modules aggregation and counters, whose lemmas the tests of the rewriting of -prove
  // below use
  lazy val database: List[Cmd] =
    val (_, parser, _) = cuvee.dafny.Source.newParser(cuvee.Config.default)
    cuvee.verify.TEQ.modules.flatMap((_, module) => cuvee.dafny.Source.parse(module, parser)) ++
      List("aggregation", "counters").flatMap(name => cuvee.dafny.Source.parse(cuvee.verify.TEQ.module(name), parser))

  val tests = Tests:
    // the lemma database is injected at the beginning, whose counter lemma rewrites the trace of i in sum.dfy;
    // that of s, which the lemma on sums of the module aggregation rewrites, is unused, its equation vanishes by the
    // one-point rule; the invariant over the counter is rewritten as well, such that only arithmetic remains
    test("lemmas"):
      val sum = Examples.root / "dafny" / "vcgen" / "sum.dfy"
      val (cmds, errors) = Examples.stream("-teq", "-include", "teq:aggregation", "-prove", "-quiet", sum.toString)
      errors ==> Nil
      assert(cmds.exists { case DefineFun(fun, _, _) => fun == Fun.trace.counter; case _ => false })
      val List(phi) = cmds.collect { case Assert(Goal, _, phi, _) => phi }: @unchecked
      assert(subexprs(phi).collect { case t: Trace => t }.isEmpty)
      assert(!subexprs(phi).exists { case App(fun, _, _, _) => fun == Fun.trace.counter; case _ => false })
      assert(!subexprs(phi).exists { case App(fun, _, _, _) => fun.name.name == "sums"; case _ => false })

      // also without loops, once, as part of the prelude of the source (see Config.injected)
      val abs = Examples.root / "dafny" / "vcgen" / "abs.dfy"
      val (cmds_, _) = Examples.stream("-teq", "-quiet", abs.toString)
      val prelude = Examples.prelude("-teq", "-quiet", abs.toString)
      assert(cuvee.verify.TEQ.lemmas.forall(prelude.contains))
      cmds_.count(cuvee.verify.TEQ.lemmas.contains) ==> cuvee.verify.TEQ.lemmas.length

    // break, continue, and return inside of loops: the loop is left by a path that ends by break or return,
    // in addition to the exit where the guard does not hold
    test("jumps"):
      for name <- List("break.dfy", "continue.dfy", "return.dfy", "invalid_break.dfy")
      do
        val file = Examples.root / "dafny" / "vcgen" / name
        val (cmds, errors) = Examples.output("-teq", "-quiet", file.toString)
        errors ==> Nil
        assert(cmds.exists { case Assert(Goal, _, _, _) => true; case _ => false })

    // the counter i of sum.dfy is recognized by the lemma of example 2.3
    test("counter"):
      val file = Examples.root / "dafny" / "vcgen" / "sum.dfy"
      val (cmds, errors) = Examples.output("-teq", "-quiet", file.toString)
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
        Trace(i, List(Butlast(Counter(Ints.zero, Ints.one, n))), x, List(k), Ints.plus(x, c)),
        Counter(i, c, n)
      )

      // the synthetic counter K == counter(0, 1, n) is followed from the premises (see Context.↑),
      // the trace of the loop variable i becomes counter(0, 1, n), only that of s remains
      val phi_ = cuvee.prove.Simplify.simplify(cuvee.Config.default, State.empty, cuvee.prove.Context.empty(State.empty).copy(polarity = Some(true)).withRules(List(rule)), phi)
      assert(subexprs(phi_).collect { case t: Trace => t }.distinct.length == 1)

    // the accessors of the folds of the module aggregation: an earlier value is the aggregate of a prefix, without the
    // fold, and the prefix of the history is the fold over the prefix of the values (earlier_maxs, prefix_maxs, ...)
    test("accessors"):
      val rules = cuvee.prove.Rules.from(State.empty, database)
      def fun(name: String) = database.collectFirst { case DeclareFun(fun, _) if fun.name.name == name => fun; case DefineFun(fun, _, _) if fun.name.name == name => fun }.get
      def app(name: String, args: Expr*) = App(fun(name), args.toList)
      def has(expr: Expr, name: String) = subexprs(expr).exists { case App(f, _, _, _) => f.name.name == name; case _ => false }

      val e = Var("e", Sort.int)
      val j = Var("j", Sort.int)
      val x = Var("x", Sort.int)
      val values = Var("values", Sort.list(Sort.int))
      val ctx = cuvee.prove.Context.empty(State.empty).withRules(rules)

      val folds = List("sums" -> List(x, values), "maxs" -> List(x, values), "mins" -> List(x, values),
        "parities" -> List(x, values), "counts" -> List(x, e, values))

      for (name, args) <- folds
      do
        val earlier = Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, app("earlier", j, Butlast(app(name, args*))))
        assert(!has(earlier, name))
        assert(subexprs(earlier).contains(app("prefix", j, values)))

        val prefix = Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, app("prefix", j, Butlast(app(name, args*))))
        assert(subexprs(prefix).contains(app(name, args.init :+ app("prefix", j, values)*)))

    // the prefix counts are the multiplicities in the multisets of prefixes (earlier_counts of the module aggregation)
    test("count"):
      val rules = cuvee.prove.Rules.from(State.empty, database)
      def fun(name: String) = database.collectFirst { case DeclareFun(fun, _) if fun.name.name == name => fun; case DefineFun(fun, _, _) if fun.name.name == name => fun }.get
      def app(name: String, args: Expr*) = App(fun(name), args.toList)
      def has(expr: Expr, name: String) = subexprs(expr).exists { case App(f, _, _, _) => f.name.name == name; case _ => false }

      val e = Var("e", Sort.int)
      val j = Var("j", Sort.int)
      val x = Var("x", Sort.int)
      val keys = Var("keys", Sort.list(Sort.int))

      val bounds = cuvee.prove.Context.empty(State.empty).withRules(rules)
      val earlier = Rewrite.rewrite(cuvee.Config.default, State.empty, bounds, app("earlier", j, Butlast(app("counts", x, e, keys))))
      assert(subexprs(earlier).contains(app("elems", app("prefix", j, keys))))
      assert(!has(earlier, "counts"))

    // the invariant of a loop condition i < 1024 over a counter is rewritten by the lemma for k < m,
    // which is m - k - 1 on Int, whereas the constant of 1023 - i is folded,
    // also with a second dependency whose bound variable is unused, and with the counter defined in the context
    test("invs with literal bound"):
      val rules = cuvee.prove.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      val n = Var("n", Sort.int)
      val trace = Sort(Con("Trace", 1), List(Sort.int))
      val I = Var("I", trace)
      val K = Var("K", trace)
      val i = Var("i", Sort.int)
      val k = Var("k", Sort.int)
      val bound = Lit(BigInt(1024), Sort.int)
      val counter = Counter(Ints.zero, Ints.one, n)
      val ctx = cuvee.prove.Context.empty(State.empty).assume(Ints.le(Ints.zero, n)).assume(Eq(I, counter)).assume(Eq(K, counter)).withRules(rules)

      for inv <- List(
          Invs(List(Butlast(counter)), List(i), Ints.lt(i, bound)),
          Invs(List(Butlast(I)), List(i), Ints.lt(i, bound)),
          Invs(List(Butlast(K), Butlast(I)), List(k, i), Ints.lt(i, bound)))
      do
        val inv_ = Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, inv)
        assert(!subexprs(inv_).exists(_.isInstanceOf[Invs]))

    // calls of callees with a contract are by the contract, those of callees without one are inlined
    test("calls with contract"):
      val file = Examples.root / "dafny" / "vcgen" / "call.dfy"
      val (cmds, errors) = Examples.output("-teq", "-quiet", file.toString)
      errors ==> Nil
      assert(cmds.exists { case Assert(Goal, _, _, _) => true; case _ => false })

    // a loop that assigns a constant: the dependency of the lemma whose bound variable the update does not use
    // is instantiated by a dependency of the expression, here the counter defined in the context (current_trace_constant
    // of the module counters)
    test("constant updates"):
      val rules = cuvee.prove.Rules.from(State.empty, database)
      val n = Var("n", Sort.int)
      val trace = Sort(Con("Trace", 1), List(Sort.int))
      val K = Var("K", trace)
      val X = Var("X", trace)
      val x = Var("x", Sort.int)
      val k = Var("k", Sort.int)
      val loop = Trace(Ints.one, List(Butlast(K)), x, List(k), Ints.zero)
      val ctx = cuvee.prove.Context.empty(State.empty).assume(Ints.le(Ints.zero, n)).assume(Eq(K, Counter(Ints.zero, Ints.one, n))).assume(Eq(X, loop)).withRules(rules)
      Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, Current(X)) ==>
        Eps(List(Upd(Ints.le(n, Ints.zero), Ints.one), Upd(Ints.lt(Ints.zero, n), Ints.zero)))
