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
    Rule(lhs.free.toList, lhs, rhs, cond)

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
      val (cmds, errors) = Examples.output("-teq", "-simplify", "-print", "null", sum.toString)
      errors ==> Nil
      assert(cmds.exists { case DeclareFun(fun, _) => fun == Fun.trace.counter; case _ => false })
      val List(phi) = cmds.collect { case Assert(Goal, _, phi, _) => phi }: @unchecked
      assert(subexprs(phi).collect { case t: Trace => t }.isEmpty)
      assert(!subexprs(phi).exists { case App(fun, _, _, _) => fun == Fun.trace.counter; case _ => false })
      assert(!subexprs(phi).exists { case App(fun, _, _, _) => fun.name.name == "sums"; case _ => false })

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
      val butlast = Butlast(K)
      val rule = rw(
        Trace(i, List(butlast), x, List(k), List(Upd(True, Plus.int(x, c)))),
        Counter(i, c, Steps(K))
      )

      val phi_ = Rewrite(List(rule), phi)
      val counters = subexprs(phi_).collect { case app @ Counter(Zero.int, One.int, _) => app }
      // the synthetic counter K = counter(0, 1, n) and the loop variable i = counter(0, 1, steps(K))
      assert(counters.exists { case Counter(_, _, Steps(_)) => true; case _ => false })
      assert(subexprs(phi_).collect { case t: Trace => t }.distinct.length == 1)

    // a variable that is increased where the values are equal to e counts the occurrences of e,
    // also on values of other types than bool, and on booleans whose guards are the values themselves
    test("counts"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
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

    // an update of a visited key replaces its contribution to the count, and the prefix counts are counts of prefixes;
    // the conditions are decided by the assumptions of the context
    test("count"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      def fun(name: String) = cuvee.verify.TEQ.lemmas.collectFirst { case DeclareFun(fun, _) if fun.name.name == name => fun }.get
      def app(name: String, args: Expr*) = App(fun(name), args.toList)
      def has(expr: Expr, name: String) = subexprs(expr).exists { case App(f, _, _, _) => f.name.name == name; case _ => false }

      val a = Var("a", Sort.array(Sort.int, Sort.int))
      val k = Var("k", Sort.int)
      val w = Var("w", Sort.int)
      val e = Var("e", Sort.int)
      val j = Var("j", Sort.int)
      val x = Var("x", Sort.int)
      val keys = Var("keys", Sort.seq(Sort.int))

      val ctx = cuvee.simplify.Ctx.empty.assume(app("distincts", keys)).withRules(rules)
      val updated = Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, app("count", e, app("selects", Store(a, k, w), keys)))
      assert(subexprs(updated).contains(app("count", e, app("selects", a, keys))))
      assert(!subexprs(updated).exists { case Store(_, _, _) => true; case _ => false })

      val bounds = cuvee.simplify.Ctx.empty.assume(Le.int(Zero.int, j)).assume(Lt.int(j, app("length", keys))).withRules(rules)
      val earlier = Rewrite.rewrite(cuvee.Config.default, State.empty, bounds, app("earlier", j, Butlast(app("counts", x, e, keys))))
      assert(subexprs(earlier).contains(app("count", e, app("prefix", j, keys))))
      assert(!has(earlier, "counts"))

    // the empty prefix is the empty sequence, whose sum is 0
    test("empty prefix"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      def fun(name: String) = cuvee.verify.TEQ.lemmas.collectFirst { case DeclareFun(fun, _) if fun.name.name == name => fun }.get
      val vs = Var("vs", Sort.seq(Sort.int))

      Rewrite(rules, App(fun("sum"), List(App(fun("prefix"), List(Zero.int, vs))))) ==> Zero.int

    // the bounds of counts and of the prefix maxima and minima are rewrite rules, the latter for earlier values
    // under the assumptions of the context
    test("bounds"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      def fun(name: String) = cuvee.verify.TEQ.lemmas.collectFirst { case DeclareFun(fun, _) if fun.name.name == name => fun }.get
      def app(name: String, args: Expr*) = App(fun(name), args.toList)

      val e = Var("e", Sort.int)
      val x = Var("x", Sort.int)
      val k = Var("k", Sort.int)
      val vs = Var("vs", Sort.seq(Sort.int))
      val count = app("count", e, vs)
      val max = app("current", app("maxs", x, vs))
      val min = app("current", app("mins", x, vs))

      Rewrite(rules, Le.int(Zero.int, count)) ==> True
      Rewrite(rules, Le.int(count, app("length", vs))) ==> True
      Rewrite(rules, Le.int(x, max)) ==> True
      Rewrite(rules, Le.int(min, x)) ==> True

      val bounds = cuvee.simplify.Ctx.empty.assume(Le.int(Zero.int, k)).assume(Lt.int(k, app("length", vs))).withRules(rules)
      Rewrite.rewrite(cuvee.Config.default, State.empty, bounds, Le.int(app("earlier", k, vs), max)) ==> True
      Rewrite.rewrite(cuvee.Config.default, State.empty, bounds, Le.int(min, app("earlier", k, vs))) ==> True

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
      val ctx = cuvee.simplify.Ctx.empty.assume(Le.int(Zero.int, n)).assume(Eq(I, counter)).assume(Eq(K, counter)).withRules(rules)

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

    // calls of procedures without a contract are inlined, such that the results are known to the caller,
    // also through a return inside of a branch, and the variables of the caller with the names of the formals are restored
    test("inlining"):
      val text =
        """int inc(int x) { if (x < 0) return 0; return x + 1; }
          |int main(void) { int x = 5; int y = inc(1); int z = inc(-3); assert(x == 5 && y == 2 && z == 0); return 0; }
          |""".stripMargin
      val file = os.temp(text, suffix = ".c")
      val (cmds, errors) = Examples.output("-teq", "-simplify", "-print", "null", file.toString)
      errors ==> Nil
      cmds.collect { case Assert(Goal, _, phi, _) => phi } ==> Nil

    // a procedure without a body cannot be inlined
    test("inlining without body"):
      val text =
        """method f(x: int) returns (y: int)
          |method g() returns (z: int) { z := f(1); }
          |""".stripMargin
      Examples.check("dfy", text, "-teq") ==> List("procedure without body")

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
      val loop = Trace(One.int, List(Butlast(K)), x, List(k), List(Upd(True, Zero.int)))
      val ctx = cuvee.simplify.Ctx.empty.assume(Le.int(Zero.int, n)).assume(Eq(K, Counter(Zero.int, One.int, n))).assume(Eq(X, loop)).withRules(rules)
      Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, Current(X)) ==> Ite(Eq(n, Zero.int), One.int, Zero.int)

    // the loop for (i = 0; i != N; i++) runs N times, from the lemma on counters that avoid a value
    test("counters that avoid a value"):
      val text =
        """int main(void) { int i; for (i = 0; i != 100; i++) { assert(i <= 100); } assert(i == 100); return 0; }
          |""".stripMargin
      val file = os.temp(text, suffix = ".c")
      val (cmds, errors) = Examples.output("-teq", "-split", "-simplify", "-print", "null", file.toString)
      errors ==> Nil
      cmds.collect { case Assert(Goal, _, phi, _) => phi } ==> Nil

    // the iterations of a counter before and from a bound, counted for a branch on it in the body (gj2007)
    test("counters before a bound"):
      val text =
        """int main(void) { int x = 0; int y = 50; int z = 0;
          |  while (x < 100) { if (x < 50) { x = x + 1; z = z + 1; } else { x = x + 1; y = y + 1; } }
          |  assert(y == 100 && z == 50); return 0; }
          |""".stripMargin
      val file = os.temp(text, suffix = ".c")
      val (cmds, errors) = Examples.output("-teq", "-split", "-simplify", "-print", "null", file.toString)
      errors ==> Nil
      cmds.collect { case Assert(Goal, _, phi, _) => phi } ==> Nil

    // the iterations from a bound on, counted for an increment in the body (Mono6_1), where solving z == x for the
    // number of iterations would be cyclic, since the count depends on the counter of the iterations
    test("counters from a bound"):
      def goals(assertion: String) =
        val text =
          s"""int main(void) { unsigned int x = 0; unsigned int z = 5;
             |  while (x < 10) { if (x >= 5) z++; x++; }
             |  assert($assertion); return 0; }
             |""".stripMargin
        val file = os.temp(text, suffix = ".c")
        val (cmds, errors) = Examples.output("-teq", "-split", "-simplify", "-print", "null", file.toString)
        errors ==> Nil
        cmds.collect { case Assert(Goal, _, phi, _) => phi }
      goals("z == x") ==> Nil
      goals("z != x") ==> List(False)

    // the variable of a counter that runs in parallel to the iterations is bounded like them,
    // since its value earlier(k, ⌊I⌋) is k within the range of k
    test("bounds of counters"):
      val text =
        """int main(void) { int s = 0; int i;
          |  for (i = 0; i < 10; i++) { if (0 <= i && i < 10) s = s + 1; else s = s + 2; }
          |  assert(s == 10); return 0; }
          |""".stripMargin
      val file = os.temp(text, suffix = ".c")
      val (cmds, errors) = Examples.output("-teq", "-split", "-simplify", "-print", "null", file.toString)
      errors ==> Nil
      cmds.collect { case Assert(Goal, _, phi, _) => phi } ==> Nil

    // a value read at one of the keys occurs among the values read at them, and a value at an index occurs in the sequence
    test("occurrences"):
      val rules = cuvee.simplify.Rules.from(State.empty, cuvee.verify.TEQ.lemmas)
      def fun(name: String) = cuvee.verify.TEQ.lemmas.collectFirst { case DeclareFun(fun, _) if fun.name.name == name => fun }.get
      def app(name: String, args: Expr*) = App(fun(name), args.toList)

      val a = Var("a", Sort.array(Sort.int, Sort.int))
      val k = Var("k", Sort.int)
      val j = Var("j", Sort.int)
      val keys = Var("keys", Sort.seq(Sort.int))

      val ctx = cuvee.simplify.Ctx.empty.assume(app("occurs", k, keys)).withRules(rules)
      Rewrite.rewrite(cuvee.Config.default, State.empty, ctx, app("occurs", Select(a, k), app("selects", a, keys))) ==> True
      Rewrite(rules, app("occurs", Earlier(j, keys), keys)) ==> True
