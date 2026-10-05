package cuvee.simplify

import util.Name
import cuvee.Error
import cuvee.Debug
import cuvee.Config
import cuvee.pipe.Transform
import cuvee.core._

// contextual simplification of the formulas in assertions and function definitions,
// where each subterm is simplified under the facts known to hold at its position
object Simplify extends Transform:
  // the assertions and lemmas with the attribute :rw so far are rewrite rules, which are kept as they are,
  // the other commands are simplified with these rules, each with a fresh number of rewrite steps,
  // where axioms, goals, and lemmas that simplify to true are dropped, since they state nothing;
  // debug output is printed with the printer of the configuration
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val rules = this.rules(prefix ++ cmds)

    for
      cmd <- cmds
      cmd_ = if isRule(cmd) then cmd else simplify(config, state, Ctx.empty.withRules(rules), cmd)
      if !isTrivial(cmd_)
    yield cmd_

  def isTrivial(cmd: Cmd) =
    cmd match
      case Assert(_, _, True, _) => true
      case _                     => false

  def isRule(cmd: Cmd) =
    cmd match
      case Assert(Axiom | Lemma, _, _, attrs) => attrs.contains("rw")
      case _                                  => false

  // the rewrite rules of the assertions and lemmas with the attribute :rw
  def rules(cmds: List[Cmd]): List[Rule] =
    for case cmd @ Assert(_, _, phi, _) <- cmds if isRule(cmd)
    yield Rule.check(rule(phi))

  // the rule of a formula: the universally quantified variables are the variables of the rule,
  // the premise of an implication is its condition, and the conclusion must be an equation l = r,
  // an equivalence l <=> r, a negation not φ (φ = false), or a boolean atom φ (φ = true)
  def rule(phi: Expr): Rule =
    phi match
      case All(_, body) =>
        rule(body)

      case Imp(cond, body) =>
        val Rule(lhs, rhs, cond_) = rule(body)
        Rule(lhs, rhs, if cond_ == True then cond else And(cond, cond_))

      case Eq(lhs, rhs) =>
        Rule(lhs, rhs)

      case Eqv(lhs, rhs) =>
        Rule(lhs, rhs)

      case Not(atom) =>
        Rule(atom, False)

      case App(fun, _, _, _) if !connectives.contains(fun.name.name) =>
        Rule(phi, True)

      case _ =>
        Error.raise("rewrite rule is not an equation, an equivalence, a negation, or a boolean atom", phi)

  // the logical connectives, which are not boolean atoms
  val connectives = Set("and", "or", "=>", "<=>", "not", "ite", "true", "false")

  // `ctx` is an empty context, which provides the rewrite rules;
  // the antecedents of assertions are assumed in the context of their succedents during simplification,
  // assertions are normalized into clauses afterwards (see Normalize),
  // since simplification may produce nested implications and negations again
  def simplify(config: Config, state: State, ctx: Ctx, cmd: Cmd): Cmd =
    cmd match
      case Assert(justify, params, phi, attrs) =>
        val phi_ = simplify(config, state, ctx.copy(polarity = Some(true)), phi)
        Assert(justify, params, Normalize(phi_), attrs)

      case DefineFun(fun, body, attrs) =>
        DefineFun(fun, simplify(config, state, ctx, body), attrs)

      case DeclareProc(proc, attrs) =>
        DeclareProc(proc, simplify(config, state, ctx, attrs))

      case DefineProc(proc, body, attrs) =>
        DefineProc(proc, simplify(config, state, ctx, body), simplify(config, state, ctx, attrs))

      case _ =>
        cmd

  // the formulas and terms in attributes, e.g. contracts and invariants, are simplified without context
  def simplify(config: Config, state: State, ctx: Ctx, attrs: Attrs): Attrs =
    attrs.map(simplify(config, state, ctx, _))

  // programs are simplified statement by statement, where the expressions are simplified without context,
  // since the facts known before an assignment may not hold afterwards;
  // branches and loops with constant tests are reduced, and statements without effect are dropped
  def simplify(config: Config, state: State, ctx: Ctx, prog: Prog): Prog =
    prog match
      case Break | Continue | Return =>
        prog

      case Spec(xs, pre, post) =>
        val pre_ = simplify(config, state, ctx, pre)
        val post_ = simplify(config, state, ctx, post)
        Spec(xs, pre_, post_)

      // assignments of variables to themselves are dropped
      case Assign(lhs, rhs) =>
        val rhs_ = rhs.map(simplify(config, state, ctx, _))
        val (lhs__, rhs__) = (lhs zip rhs_).filterNot((x, e) => x == e).unzip
        Assign(lhs__, rhs__)

      case Call(name, args, res) =>
        val args_ = args.map(simplify(config, state, ctx, _))
        Call(name, args_, res)

      // nested blocks without locals are merged, statements without effect are dropped
      case Block(locals, progs) =>
        val progs_ =
          progs.map(simplify(config, state, ctx, _)).flatMap:
            case Block(Nil, inner)                       => inner
            case Assign(Nil, Nil) | Spec(Nil, True, True) => Nil
            case prog_                                   => List(prog_)
        val locals_ = locals.filter(x => progs_.exists(_.free.contains(x)))
        Block(locals_, progs_)

      case Choice(progs) =>
        val progs_ = progs.map(simplify(config, state, ctx, _))
        Choice(progs_)

      case If(test, left, right) =>
        val test_ = simplify(config, state, ctx, test)
        test_ match
          case True =>
            simplify(config, state, ctx, left)

          case False =>
            simplify(config, state, ctx, right)

          case _ =>
            val left_ = simplify(config, state, ctx, left)
            val right_ = simplify(config, state, ctx, right)
            If(test_, left_, right_)

      case While(test, body, attrs) =>
        val test_ = simplify(config, state, ctx, test)
        test_ match
          case False =>
            Block(Nil, Nil)

          case _ =>
            val body_ = simplify(config, state, ctx, body)
            val attrs_ = simplify(config, state, ctx, attrs)
            While(test_, body_, attrs_)

      case Iter(body, attrs) =>
        val body_ = simplify(config, state, ctx, body)
        val attrs_ = simplify(config, state, ctx, attrs)
        Iter(body_, attrs_)

      case Ode(xs, rhs, dom, attrs) =>
        val rhs_ = rhs.map(simplify(config, state, ctx, _))
        val dom_ = simplify(config, state, ctx, dom)
        val attrs_ = simplify(config, state, ctx, attrs)
        Ode(xs, rhs_, dom_, attrs_)

      case Par(calls) =>
        val calls_ =
          for Call(name, args, res) <- calls
          yield Call(name, args.map(simplify(config, state, ctx, _)), res)
        Par(calls_)

  // simplify `expr` assuming that all facts in `ctx` hold
  // by repeated rounds of simplification until a fixpoint is reached,
  // a formula that is known from the context is replaced by its truth value;
  // after each round, a rewrite rule of the context is applied at the top, whose subterms are simplified already
  def simplify(config: Config, state: State, ctx: Ctx, expr: Expr): Expr =
    ctx.lookup(expr) match
      case Some(true)  => True
      case Some(false) => False
      case None =>
        val once_ = once(config, state, ctx, expr)
        if once_ != expr
        then Debug.info("simplify", show(config.printer, expr) + "  ~>  " + show(config.printer, once_))

        val expr_ = rewrite(config, state, ctx, once_)
        if expr_ == expr
        then expr
        else simplify(config, state, ctx, expr_)

  // expressions in debug output, on a single line
  def show(printer: cuvee.pipe.Printer, expr: Expr): String =
    printer.lines(expr).map(_.trim).mkString(" ")

  // a single step with the rewrite rules of the context at the top of `expr`,
  // where the conditions of the rules are decided by simplification in the context (see Rewrite)
  def rewrite(config: Config, state: State, ctx: Ctx, expr: Expr): Expr =
    Rewrite.step(config, state, ctx, expr)

  // a single round of simplification, dispatching on the builtin functions,
  // subterms are simplified first, where ite and the boolean connectives
  // extend the context by the facts known at the position of each subterm,
  // negation and the premise of implication flip the polarity,
  // and the arguments of other functions have none
  def once(config: Config, state: State, ctx: Ctx, expr: Expr): Expr =
    expr match
      case x: Var =>
        var_(config, state, ctx, x)

      case _: Lit | True | False =>
        expr

      case Eq(left, right) =>
        val left_ = simplify(config, state, ctx.neutral, left)
        val right_ = simplify(config, state, ctx.neutral, right)
        eq_(config, state, ctx, left_, right_)

      case Eqv(left, right) =>
        val left_ = simplify(config, state, ctx.neutral, left)
        val right_ = simplify(config, state, ctx.neutral, right)
        eqv(config, state, ctx, left_, right_)

      case Distinct(exprs) =>
        val exprs_ = exprs.map(simplify(config, state, ctx.neutral, _))
        distinct(config, state, ctx, exprs_)

      case Is(arg, fun) =>
        val arg_ = simplify(config, state, ctx.neutral, arg)
        is(config, state, ctx, arg_, fun)

      // the derivative is taken of the simplified argument, e.g. after > is turned into <
      case Diff(xs, arg) =>
        val arg_ = simplify(config, state, ctx.neutral, arg)
        diff(config, state, xs, arg_)

      case Old(arg) =>
        Old(simplify(config, state, ctx.neutral, arg))

      // the annotation does not change the value, hence the polarity is kept
      case As(arg, typ) =>
        val arg_ = simplify(config, state, ctx, arg)
        As(arg_, typ)

      case Ite(test, left, right) =>
        val test_ = simplify(config, state, ctx.neutral, test)
        val left_ = simplify(config, state, ctx.assume(List(test_), Nil), left)
        val right_ = simplify(config, state, ctx.assume(Nil, List(test_)), right)
        ite(config, state, ctx, test_, left_, right_)

      case Select(base, index) =>
        val base_ = simplify(config, state, ctx.neutral, base)
        val index_ = simplify(config, state, ctx.neutral, index)
        select(config, state, ctx, base_, index_)

      case Store(base, index, value) =>
        val base_ = simplify(config, state, ctx.neutral, base)
        val index_ = simplify(config, state, ctx.neutral, index)
        val value_ = simplify(config, state, ctx.neutral, value)
        store(config, state, ctx, base_, index_, value_)

      case Not(phi) =>
        val phi_ = simplify(config, state, ctx.flip, phi)
        not(config, state, ctx, phi_)

      case Imp(phi, psi) =>
        // like a disjunction of not phi and psi:
        // the premise is simplified assuming that the conclusion does not hold,
        // and the conclusion is simplified assuming the simplified premise
        val phi_ = simplify(config, state, ctx.flip.assume(Nil, List(psi)), phi)
        val psi_ = simplify(config, state, ctx.assume(List(phi_), Nil), psi)
        imp(config, state, ctx, phi_, psi_)

      case And(phis) =>
        val phis_ = nary(config, state, ctx, Nil, phis, true)
        and(config, state, ctx, phis_)

      case Or(phis) =>
        val phis_ = nary(config, state, ctx, Nil, phis, false)
        or(config, state, ctx, phis_)

      // on Real, division by a nonzero literal is part of the polynomials
      case UMinus.int(_) | Plus.int(_) | Minus.int(_, _) | Times.int(_) |
          UMinus.real(_) | Plus.real(_) | Minus.real(_, _) | Times.real(_) | DivBy.real(_, _) =>
        arith(config, state, ctx.neutral, expr)

      case DivBy.int(left, right) =>
        val left_ = arith(config, state, ctx.neutral, left)
        val right_ = arith(config, state, ctx.neutral, right)
        div(config, state, ctx, left_, right_)

      case Mod.int(left, right) =>
        val left_ = arith(config, state, ctx.neutral, left)
        val right_ = arith(config, state, ctx.neutral, right)
        mod(config, state, ctx, left_, right_)

      case Lt.int(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Ring.int, left, right)
        lt(config, state, ctx, Ring.int, Lt.int, poly_)

      case Lt.real(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Ring.real, left, right)
        lt(config, state, ctx, Ring.real, Lt.real, poly_)

      case Le.int(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Ring.int, left, right)
        le(config, state, ctx, Ring.int, Le.int, poly_)

      case Le.real(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Ring.real, left, right)
        le(config, state, ctx, Ring.real, Le.real, poly_)

      case Gt.int(left, right) =>
        Lt.int(right, left)

      case Gt.real(left, right) =>
        Lt.real(right, left)

      case Ge.int(left, right) =>
        Le.int(right, left)

      case Ge.real(left, right) =>
        Le.real(right, left)

      case App(fun, inst, typ, args) =>
        val args_ = args.map(simplify(config, state, ctx.neutral, _))
        app(config, state, ctx, fun, inst, typ, args_)

      // bound variables are renamed apart from the context before entering the body
      case Bind(quant, bound, body) =>
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(config, state, ctx.bind(bound_), re(body))
        bind(config, state, ctx, quant, bound_, body_)

      case Let(bound, args, body) =>
        val args_ = args.map(simplify(config, state, ctx.neutral, _))
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(config, state, ctx.bind(bound_), re(body))
        let(config, state, ctx, bound_, args_, body_)

      // the variables of the patterns are renamed apart like bound variables, and the bodies assume their condition
      case Match(arg, cases) =>
        val arg_ = simplify(config, state, ctx.neutral, arg)
        val cases_ =
          for Case(pat, body, cond) <- cases
          yield
            val (bound_, re) = ctx.avoid(pat.free.toList)
            val cond_ = simplify(config, state, ctx.neutral.bind(bound_), re(cond))
            val body_ = simplify(config, state, ctx.bind(bound_).assume(List(cond_), Nil), re(body))
            case_(config, state, ctx, re(pat), body_, cond_)
        match_(config, state, ctx, arg_, cases_)

      // the combinators bind the accumulator and the variables for the dependencies like quantifiers
      case Trace(init, deps, acc, bound, updates) =>
        val init_ = simplify(config, state, ctx.neutral, init)
        val deps_ = deps.map(simplify(config, state, ctx.neutral, _))
        val (vars_, re) = ctx.avoid(acc :: bound)
        val updates_ = this.updates(config, state, ctx.neutral.bind(vars_), updates.map(_.map(re(_))))
        trace(config, state, ctx, init_, deps_, vars_.head, vars_.tail, updates_)

      case Maps(deps, bound, updates) =>
        val deps_ = deps.map(simplify(config, state, ctx.neutral, _))
        val (bound_, re) = ctx.avoid(bound)
        val updates_ = this.updates(config, state, ctx.neutral.bind(bound_), updates.map(_.map(re(_))))
        maps(config, state, ctx, deps_, bound_, updates_)

      // the body holds for all values of the dependencies, like the body of a universal quantifier
      case Invs(deps, bound, body) =>
        val deps_ = deps.map(simplify(config, state, ctx.neutral, _))
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(config, state, ctx.bind(bound_), re(body))
        invs(config, state, ctx, deps_, bound_, body_)

  // the guards of the cases of an update are simplified, cases whose guard is false are dropped,
  // and the results are simplified assuming their guard
  def updates(config: Config, state: State, ctx: Ctx, updates: List[Upd]): List[Upd] =
    for
      Upd(cond, rhs) <- updates
      cond_ = simplify(config, state, ctx, cond)
      if cond_ != False
    yield upd(config, state, ctx, cond_, simplify(config, state, ctx.assume(List(cond_), Nil), rhs))

  // simplify each of `phis` assuming the others, which hold if `pos` (conjunction)
  // and do not hold otherwise (disjunction);
  // propositions in `done` are already processed (in reverse) and assumed in their simplified form,
  // otherwise e.g. both copies in `a and a` would simplify to true
  def nary(config: Config, state: State, ctx: Ctx, done: List[Expr], phis: List[Expr], pos: Boolean): List[Expr] =
    phis match
      case Nil =>
        done.reverse

      case phi :: rest =>
        val others = done ++ rest
        val ctx_ =
          if pos
          then ctx.assume(others, Nil)
          else ctx.assume(Nil, others)
        val phi_ = simplify(config, state, ctx_, phi)
        nary(config, state, ctx, phi_ :: done, rest, pos)

  // simplify an integer- or real-valued term into the normal form of polynomials,
  // terms of other types, e.g. of defined sorts, are simplified only
  def arith(config: Config, state: State, ctx: Ctx, expr: Expr): Expr =
    Ring(expr.typ) match
      case Some(ring) => poly(config, state, ctx, ring, expr).normalize.toExpr(ring)
      case None       => simplify(config, state, ctx, expr)

  // simplify an integer- or real-valued term into a polynomial (not normalized):
  // descend through +, -, * and literals, simplify the leaves,
  // which may in turn become arithmetic expressions, and combine the results;
  // on Real, division by a term that simplifies to a nonzero literal is multiplication by its inverse
  def poly(config: Config, state: State, ctx: Ctx, ring: Ring, expr: Expr): Poly =
    ring.num(expr) match
      case Some(n) =>
        Poly.const(n)

      case None =>
        expr match
          case ring.uminus(arg) =>
            val arg_ = poly(config, state, ctx, ring, arg)
            -arg_

          case ring.plus(args) =>
            val args_ = args.map(poly(config, state, ctx, ring, _))
            args_.foldLeft(Poly.zero)(_ + _)

          case ring.minus(left, right) =>
            val left_ = poly(config, state, ctx, ring, left)
            val right_ = poly(config, state, ctx, ring, right)
            left_ - right_

          case ring.times(args) =>
            val args_ = args.map(poly(config, state, ctx, ring, _))
            args_.foldLeft(Poly.one)(_ * _)

          case DivBy.real(left, right) =>
            val left_ = poly(config, state, ctx, ring, left)
            val right_ = simplify(config, state, ctx, right)
            ring.num(right_) match
              case Some(r) if !r.isZero => left_ * (util.Rational(1) / r)
              case _                    => Poly.atom(DivBy.real(left_.normalize.toExpr(ring), right_))

          case _ =>
            val expr_ = simplify(config, state, ctx, expr)
            Arith.toPoly(ring, expr_)

  // variables known to be equal to another one are replaced
  def var_(config: Config, state: State, ctx: Ctx, x: Var): Expr =
    ctx.su.vars.get(x) match
      case Some(y) => y
      case None    => x

  def eq_(config: Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case _ if left == right =>
        True

      case (Lit(a, _), Lit(b, _)) =>
        if a == b then True else False

      case (True, False) | (False, True) =>
        False

      case (_, True) => left
      case (True, _) => right
      case (_, False) => Not(left)
      case (False, _) => Not(right)

      case _ =>
        Eq(left, right)

  // equivalences are equations on Bool, the normal form, such that both are known from the context alike,
  // and as which SMT-LIB writes them
  def eqv(config: Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    eq_(config, state, ctx, left, right)

  // false if two of the expressions are equal, true if all of them are pairwise different,
  // e.g. literals, two expressions are distinct exactly if they are not equal
  def distinct(config: Config, state: State, ctx: Ctx, exprs: List[Expr]): Expr =
    val eqs = for case a :: rest <- exprs.tails.toList; b <- rest yield eq_(config, state, ctx, a, b)

    if eqs contains True
    then False
    else if eqs forall (_ == False)
    then True
    else
      exprs match
        case List(a, b) => Not(Eq(a, b))
        case _          => Distinct(exprs)

  // testers on constructor applications
  def is(config: Config, state: State, ctx: Ctx, arg: Expr, fun: Fun): Expr =
    constr(config, state, arg) match
      case Some(constr) if constr.name == fun.name => True
      case Some(constr)                            => False
      case None                                    => Is(arg, fun)

  // the constructor that `expr` is built by, looking through type annotations
  def constr(config: Config, state: State, expr: Expr): Option[Fun] =
    expr match
      case As(expr_, _) =>
        constr(config, state, expr_)

      case App(fun, _, _, _) if state.constrs contains fun.name =>
        Some(fun)

      case _ =>
        None

  def ite(config: Config, state: State, ctx: Ctx, test: Expr, left: Expr, right: Expr): Expr =
    (test, left, right) match
      case (True, _, _)          => left
      case (False, _, _)         => right
      case _ if left == right    => left
      case (_, True, False)      => test
      case (_, False, True)      => Not(test)
      case _                     => Ite(test, left, right)

  // read over write
  def select(config: Config, state: State, ctx: Ctx, base: Expr, index: Expr): Expr =
    base match
      case Store(_, index_, value) if index_ == index =>
        value

      case Store(base_, index_, _) if eq_(config, state, ctx, index_, index) == False =>
        Select(base_, index)

      case _ =>
        Select(base, index)

  def store(config: Config, state: State, ctx: Ctx, base: Expr, index: Expr, value: Expr): Expr =
    (base, value) match
      // overwritten
      case (Store(base_, index_, _), _) if index_ == index =>
        Store(base_, index, value)

      // writes back what is already stored
      case (_, Select(base_, index_)) if base_ == base && index_ == index =>
        base

      case _ =>
        Store(base, index, value)

  def not(config: Config, state: State, ctx: Ctx, phi: Expr): Expr =
    phi match
      case True     => False
      case False    => True
      case Not(psi) => psi
      case _        => Not(phi)

  def imp(config: Config, state: State, ctx: Ctx, phi: Expr, psi: Expr): Expr =
    (phi, psi) match
      case (True, _)          => psi
      case (False, _)         => True
      case (_, True)          => True
      case (_, False)         => Not(phi)
      case _ if phi == psi    => True
      case _                  => Imp(phi, psi)

  // flatten nested conjunctions, drop true and duplicates, false makes the whole conjunction false;
  // complementary pairs are decided already, since each conjunct is simplified assuming the others (see nary)
  def and(config: Config, state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.flatMap(And.flattenStrong).distinct
    if phis_.contains(False)
    then False
    else And(phis_)

  // dual to and
  def or(config: Config, state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.flatMap(Or.flattenStrong).distinct
    if phis_.contains(True)
    then True
    else Or(phis_)

  // SMT-LIB semantics: for n != 0, m = n * (m div n) + (m mod n) with 0 <= m mod n < |n|,
  // division by zero is unspecified and therefore left alone
  def div(config: Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) if n != 0 =>
        val r = m mod n.abs
        Lit((m - r) / n, Sort.int)

      case (_, Lit(n: BigInt, _)) if n == 1 =>
        left

      // normalized in the next round
      case (_, Lit(n: BigInt, _)) if n == -1 =>
        UMinus.int(left)

      case _ =>
        DivBy.int(left, right)

  def mod(config: Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) if n != 0 =>
        Lit(m mod n.abs, Sort.int)

      case (_, Lit(n: BigInt, _)) if n == 1 || n == -1 =>
        Zero.int

      case _ =>
        Mod.int(left, right)

  // the derivative of `expr` with respect to `xs` (see Diff), by the rules of dL:
  // derivatives are on Real only, derivatives of terms on Int are kept;
  // terms that do not contain xs have derivative 0, a variable x in xs has derivative x',
  // derivatives are linear, products follow the product rule,
  // and the derivative of e < f and of e <= f is e' <= f', that of a conjunction is the conjunction of the derivatives;
  // derivatives of other expressions are kept, e.g. of applications of other functions and of division
  def diff(config: Config, state: State, xs: List[Var], expr: Expr): Expr =
    expr match
      case _ if expr.typ == Sort.real && (expr.free intersect xs.toSet).isEmpty =>
        Zero.real

      case x: Var if x.typ == Sort.real =>
        x.primed

      case UMinus.real(arg) =>
        val arg_ = diff(config, state, xs, arg)
        UMinus.real(arg_)

      case Plus.real(args) =>
        val args_ = args.map(diff(config, state, xs, _))
        Plus.real(args_)

      case Minus.real(left, right) =>
        val left_ = diff(config, state, xs, left)
        val right_ = diff(config, state, xs, right)
        Minus.real(left_, right_)

      // (a * b * c)' = a' * b * c + a * b' * c + a * b * c'
      case Times.real(args) =>
        val summands =
          for (arg, i) <- args.zipWithIndex
          yield
            val arg_ = diff(config, state, xs, arg)
            Times.real(args.updated(i, arg_))
        Plus.real(summands)

      case Lt.real(left, right) =>
        val left_ = diff(config, state, xs, left)
        val right_ = diff(config, state, xs, right)
        Le.real(left_, right_)

      case Le.real(left, right) =>
        val left_ = diff(config, state, xs, left)
        val right_ = diff(config, state, xs, right)
        Le.real(left_, right_)

      case And(phis) =>
        val phis_ = phis.map(diff(config, state, xs, _))
        And(phis_)

      case _ =>
        Diff(xs, expr)

  // the difference right - left of the sides of a comparison as a normalized polynomial
  def difference(config: Config, state: State, ctx: Ctx, ring: Ring, left: Expr, right: Expr): Poly =
    val left_ = poly(config, state, ctx, ring, left)
    val right_ = poly(config, state, ctx, ring, right)
    (right_ - left_).normalize

  // comparisons 0 < p and 0 <= p on Int or Real, built by `op`, are constants if p is,
  // otherwise they are re-arranged so that both sides have positive coefficients only,
  // e.g. 0 < y - x + 1 becomes x < y + 1
  // on Int, n < m + 1 is n <= m
  def lt(config: Config, state: State, ctx: Ctx, ring: Ring, op: Sugar.binary, poly: Poly): Expr =
    if poly.monos.isEmpty
    then if poly.const.isPositive then True else False
    else
      val (left, right) = poly.sides
      (ring, right.toExpr(ring)) match
        case (Ring.int, Succ(right_)) => Le.int(left.toExpr(ring), right_)
        case (_, right_)              => op(left.toExpr(ring), right_)

  // on Int, n + 1 <= m is n < m
  def le(config: Config, state: State, ctx: Ctx, ring: Ring, op: Sugar.binary, poly: Poly): Expr =
    if poly.monos.isEmpty
    then if poly.const.isNegative then False else True
    else
      val (left, right) = poly.sides
      (ring, left.toExpr(ring)) match
        case (Ring.int, Succ(left_)) => Lt.int(left_, right.toExpr(ring))
        case (_, left_)              => op(left_, right.toExpr(ring))

  // applications of other functions, e.g. user-defined ones
  def app(config: Config, state: State, ctx: Ctx, fun: Fun, inst: List[Type], typ: Type, args: List[Expr]): Expr =
    App(fun, inst, typ, args)

  // unused bound variables are dropped,
  // the binder vanishes when none remain (sorts are nonempty in SMT-LIB)
  def bind(config: Config, state: State, ctx: Ctx, quant: Name, bound: List[Var], body: Expr): Expr =
    val bound_ = bound.filter(body.free.contains)
    if bound_.isEmpty
    then body
    else Bind(quant, bound_, body)

  // unused bindings are dropped
  def let(config: Config, state: State, ctx: Ctx, bound: List[Var], args: List[Expr], body: Expr): Expr =
    val pairs = (bound zip args).filter((x, _) => body.free contains x)
    if pairs.isEmpty
    then body
    else Let(pairs.map(_._1), pairs.map(_._2), body)

  def case_(config: Config, state: State, ctx: Ctx, pat: Expr, body: Expr, cond: Expr): Case =
    Case(pat, body, cond)

  def match_(config: Config, state: State, ctx: Ctx, arg: Expr, cases: List[Case]): Expr =
    Match(arg, cases)

  def upd(config: Config, state: State, ctx: Ctx, cond: Expr, rhs: Expr): Upd =
    Upd(cond, rhs)

  def trace(config: Config, state: State, ctx: Ctx, init: Expr, deps: List[Expr], acc: Var, bound: List[Var], updates: List[Upd]): Expr =
    Trace(init, deps, acc, bound, updates)

  def maps(config: Config, state: State, ctx: Ctx, deps: List[Expr], bound: List[Var], updates: List[Upd]): Expr =
    Maps(deps, bound, updates)

  // invariants that hold trivially
  def invs(config: Config, state: State, ctx: Ctx, deps: List[Expr], bound: List[Var], body: Expr): Expr =
    if body == True
    then True
    else Invs(deps, bound, body)
