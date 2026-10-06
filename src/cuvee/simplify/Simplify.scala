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
    yield
      val Rule(xs, lhs, rhs, cond) = rule(phi)
      // type annotations e as T are dropped from the left-hand sides of rules, they are needed for typing only,
      // and matching would compare their types literally, which may contain the type parameters of the rule
      Rule.check(Rule(xs, lhs.removeAs, rhs, cond))

  // the rule of a formula: the universally quantified variables are the variables of the rule,
  // the premise of an implication is its condition, and the conclusion must be an equation l = r,
  // an equivalence l <=> r, a negation not φ (φ = false), or a boolean atom φ (φ = true)
  def rule(phi: Expr): Rule =
    rule(Nil, phi)

  // `xs` are the universally quantified variables so far, the variables of the rule
  def rule(xs: List[Var], phi: Expr): Rule =
    phi match
      case All(bound, body) =>
        rule(xs ++ bound, body)

      case Imp(cond, body) =>
        val Rule(_, lhs, rhs, cond_) = rule(xs, body)
        Rule(xs, lhs, rhs, if cond_ == True then cond else And(cond, cond_))

      case Eq(lhs, rhs) =>
        Rule(xs, lhs, rhs, True)

      case Eqv(lhs, rhs) =>
        Rule(xs, lhs, rhs, True)

      case Not(atom) =>
        Rule(xs, atom, False, True)

      case App(fun, _, _, _) if !connectives.contains(fun.name.name) =>
        Rule(xs, phi, True, True)

      case _ =>
        Error.raise("rewrite rule is not an equation, an equivalence, a negation, or a boolean atom", phi)

  // the logical connectives, which are not boolean atoms
  val connectives = Set("and", "or", "=>", "<=>", "not", "ite", "true", "false")

  // `ctx` is an empty context, which provides the rewrite rules;
  // the antecedents of assertions are assumed in the context of their succedents during simplification
  def simplify(config: Config, state: State, ctx: Ctx, cmd: Cmd): Cmd =
    cmd match
      case Assert(justify, params, phi, attrs) =>
        Assert(justify, params, apply(config, state, ctx.copy(polarity = Some(true)), Normalize(phi)), attrs)

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
  // the helpers below normalize their own constructor, as those of expressions
  def simplify(config: Config, state: State, ctx: Ctx, prog: Prog): Prog =
    prog match
      case Break | Continue | Return =>
        prog

      case Spec(xs, pre, post) =>
        val pre_ = simplify(config, state, ctx, pre)
        val post_ = simplify(config, state, ctx, post)
        spec(config, state, ctx, xs, pre_, post_)

      case Assign(lhs, rhs) =>
        val rhs_ = rhs.map(simplify(config, state, ctx, _))
        assign(config, state, ctx, lhs, rhs_)

      case Call(name, args, res) =>
        val args_ = args.map(simplify(config, state, ctx, _))
        call(config, state, ctx, name, args_, res)

      case Block(locals, progs) =>
        val progs_ = progs.map(simplify(config, state, ctx, _))
        block(config, state, ctx, locals, progs_)

      case Choice(progs) =>
        val progs_ = progs.map(simplify(config, state, ctx, _))
        choice(config, state, ctx, progs_)

      case If(test, left, right) =>
        val test_ = simplify(config, state, ctx, test)
        val left_ = simplify(config, state, ctx, left)
        val right_ = simplify(config, state, ctx, right)
        if_(config, state, ctx, test_, left_, right_)

      case While(test, body, attrs) =>
        val test_ = simplify(config, state, ctx, test)
        val body_ = simplify(config, state, ctx, body)
        val attrs_ = simplify(config, state, ctx, attrs)
        while_(config, state, ctx, test_, body_, attrs_)

      case Iter(body, attrs) =>
        val body_ = simplify(config, state, ctx, body)
        val attrs_ = simplify(config, state, ctx, attrs)
        iter(config, state, ctx, body_, attrs_)

      case Ode(time, xs, rhs, dom, attrs) =>
        val rhs_ = rhs.map(simplify(config, state, ctx, _))
        val dom_ = simplify(config, state, ctx, dom)
        val attrs_ = simplify(config, state, ctx, attrs)
        ode(config, state, ctx, time, xs, rhs_, dom_, attrs_)

      case Par(calls) =>
        val calls_ =
          for Call(name, args, res) <- calls
          yield Call(name, args.map(simplify(config, state, ctx, _)), res)
        par(config, state, ctx, calls_)

  // the statement without effect
  val skip = Block(Nil, Nil)

  // havoc of no variables under the trivial contract has no effect
  def spec(config: Config, state: State, ctx: Ctx, xs: List[Var], pre: Expr, post: Expr): Prog =
    (xs, pre, post) match
      case (Nil, True, True) => skip
      case _                 => Spec(xs, pre, post)

  // assignments of variables to themselves are dropped, and no assignment has no effect
  def assign(config: Config, state: State, ctx: Ctx, lhs: List[Var], rhs: List[Expr]): Prog =
    val (lhs_, rhs_) = (lhs zip rhs).filterNot((x, e) => x == e).unzip
    if lhs_.isEmpty
    then skip
    else Assign(lhs_, rhs_)

  def call(config: Config, state: State, ctx: Ctx, name: Name, args: List[Expr], res: List[Var]): Prog =
    Call(name, args, res)

  // nested blocks are merged, which drops skip, the empty block, and whose locals are hoisted unless that captures
  // variables of the other statements; statements after a jump and locals that are not used are dropped;
  // a block of a single statement without locals is that statement
  def block(config: Config, state: State, ctx: Ctx, locals: List[Var], progs: List[Prog]): Prog =
    def flatten(locals: List[Var], done: List[Prog], progs: List[Prog]): (List[Var], List[Prog]) =
      progs match
        case Nil =>
          (locals, done)

        case (jump @ (Break | Continue | Return)) :: _ =>
          (locals, done :+ jump)

        case Block(inner, progs_) :: rest
            if (inner intersect locals).isEmpty && !(done ++ rest).exists(p => inner.exists(p.free.contains)) =>
          flatten(locals ++ inner, done, progs_ ++ rest)

        case prog :: rest =>
          flatten(locals, done :+ prog, rest)

    val (locals_, progs_) = flatten(locals, Nil, progs)
    val used = locals_.filter(x => progs_.exists(_.free.contains(x)))
    (used, progs_) match
      case (Nil, List(prog)) => prog
      case _                 => Block(used, progs_)

  // nested choices are merged, duplicates are dropped, and a choice of a single statement is that statement
  def choice(config: Config, state: State, ctx: Ctx, progs: List[Prog]): Prog =
    Choice.flatten(progs).distinct match
      case List(prog) => prog
      case progs__    => Choice(progs__)

  // constant tests select a branch, equal branches make the test irrelevant,
  // and a negated test swaps the branches
  def if_(config: Config, state: State, ctx: Ctx, test: Expr, left: Prog, right: Prog): Prog =
    test match
      case True                => left
      case False               => right
      case _ if left == right  => left
      case Not(test_)          => If(test_, right, left)
      case _                   => If(test, left, right)

  // a loop that is never entered has no effect
  def while_(config: Config, state: State, ctx: Ctx, test: Expr, body: Prog, attrs: Attrs): Prog =
    test match
      case False => skip
      case _     => While(test, body, attrs)

  def iter(config: Config, state: State, ctx: Ctx, body: Prog, attrs: Attrs): Prog =
    Iter(body, attrs)

  def ode(config: Config, state: State, ctx: Ctx, time: Var, xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs): Prog =
    Ode(time, xs, rhs, dom, attrs)

  def par(config: Config, state: State, ctx: Ctx, calls: List[Call]): Prog =
    Par(calls)

  // the outer loop for assertions, which are normalized into clauses (see Normalize) before and after each round,
  // since simplification may produce nested implications and negations again,
  // and which are simplified again as long as they change, e.g. the equations of let are then known in the context;
  // normalizing before simplification removes let at positions with a polarity, whose body is neutral otherwise
  def apply(config: Config, state: State, ctx: Ctx, phi: Expr): Expr =
    val phi_ = Normalize(simplify(config, state, ctx, phi))
    if phi_ == phi
    then phi
    else apply(config, state, ctx, phi_)

  // simplify `expr` assuming that all facts in `ctx` hold
  // by repeated rounds of simplification until a fixpoint is reached,
  // a formula that is known from the context is replaced by its truth value (only formulas, which not applies to);
  // after each round, a rewrite rule of the context is applied at the top, whose subterms are simplified already
  def simplify(config: Config, state: State, ctx: Ctx, expr: Expr): Expr =
    if expr.typ == Sort.bool && implied(config, state, ctx, expr)
    then True
    else if expr.typ == Sort.bool && denied(config, state, ctx, expr)
    then False
    else
      val once_ = once(config, state, ctx, expr)
      if once_ != expr
      then Debug.step("simplify", show(config.printer, expr), show(config.printer, once_))

      val expr_ = rewrite(config, state, ctx, once_)
      if expr_ == expr
      then expr
      else simplify(config, state, ctx, expr_)

  // whether `phi` is known to hold in `ctx`, also by its negation in normal form, e.g. a < b if !(b <= a) is known,
  // in an inconsistent context at positive positions, where any formula may be chosen (polarity is only defined for formulas)
  def implied(config: Config, state: State, ctx: Ctx, phi: Expr): Boolean =
    phi == True
      || (ctx.inconsistent && ctx.polarity == Some(true))
      || (ctx.assms contains phi)
      || (ctx.concls contains not(config, state, ctx, phi))

  // whether `phi` is known not to hold in `ctx`, dually, e.g. a < b if b <= a is known
  def denied(config: Config, state: State, ctx: Ctx, phi: Expr): Boolean =
    phi == False
      || (ctx.inconsistent && ctx.polarity == Some(false))
      || (ctx.concls contains phi)
      || (ctx.assms contains not(config, state, ctx, phi))

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

      // equations on Int and Real are compared as polynomials, like < and <=
      case Eq(left, right) if left.typ == Sort.int =>
        val poly_ = difference(config, state, ctx.neutral, Ring.int, left, right)
        eq(config, state, ctx, Ring.int, poly_)

      case Eq(left, right) if left.typ == Sort.real =>
        val poly_ = difference(config, state, ctx.neutral, Ring.real, left, right)
        eq(config, state, ctx, Ring.real, poly_)

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

      // the branches have no polarity, since the context does not record the other branch (see Ctx.neutral)
      case Ite(test, left, right) =>
        val test_ = simplify(config, state, ctx.neutral, test)
        val left_ = simplify(config, state, ctx.neutral.assume(List(test_), Nil), left)
        val right_ = simplify(config, state, ctx.neutral.assume(Nil, List(test_)), right)
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

      case UMinus.int(_) | Plus.int(_) | Minus.int(_, _) | Times.int(_) =>
        arith(config, state, ctx.neutral, expr)

      // on Real, division by a nonzero literal is part of the polynomials
      case UMinus.real(_) | Plus.real(_) | Minus.real(_, _) | Times.real(_) | DivBy.real(_, _) =>
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
      case All(bound, body) =>
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(config, state, ctx.forall(bound_), re(body))
        all(config, state, ctx, bound_, body_)

      case Ex(bound, body) =>
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(config, state, ctx.exists(bound_), re(body))
        ex(config, state, ctx, bound_, body_)

      // the body has no polarity, since the context does not record the bindings
      case Let(bound, args, body) =>
        val args_ = args.map(simplify(config, state, ctx.neutral, _))
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(config, state, ctx.neutral.bind(bound_), re(body))
        let(config, state, ctx, bound_, args_, body_)

      // the variables of the patterns are renamed apart like bound variables, and the bodies assume their condition,
      // without polarity, since the context does not record the argument
      case Match(arg, cases) =>
        val arg_ = simplify(config, state, ctx.neutral, arg)
        val cases_ =
          for Case(pat, body, cond) <- cases
          yield
            val (bound_, re) = ctx.avoid(pat.free.toList)
            val cond_ = simplify(config, state, ctx.neutral.bind(bound_), re(cond))
            val body_ = simplify(config, state, ctx.neutral.bind(bound_).assume(List(cond_), Nil), re(body))
            case_(config, state, ctx, re(pat), body_, cond_)
        match_(config, state, ctx, arg_, cases_)

      // the combinators bind the accumulator and the variables for the dependencies like quantifiers,
      // their updates and bodies assume the invariants of the context over the same dependencies (see invariants)
      case Trace(init, deps, acc, bound, updates) =>
        val init_ = simplify(config, state, ctx.neutral, init)
        val deps_ = deps.map(simplify(config, state, ctx.neutral, _))
        val (vars_, re) = ctx.avoid(acc :: bound)
        val ctx_ = ctx.neutral.bind(vars_).assume(invariants(ctx, deps_, vars_.tail), Nil)
        val updates_ = this.updates(config, state, ctx_, updates.map(_.map(re(_))))
        trace(config, state, ctx, init_, deps_, vars_.head, vars_.tail, updates_)

      case Maps(deps, bound, updates) =>
        val deps_ = deps.map(simplify(config, state, ctx.neutral, _))
        val (bound_, re) = ctx.avoid(bound)
        val ctx_ = ctx.neutral.bind(bound_).assume(invariants(ctx, deps_, bound_), Nil)
        val updates_ = this.updates(config, state, ctx_, updates.map(_.map(re(_))))
        maps(config, state, ctx, deps_, bound_, updates_)

      // the body holds for all values of the dependencies, like the body of a universal quantifier,
      // but without polarity, since the dependencies are not recorded in the context
      case Invs(deps, bound, body) =>
        val deps_ = deps.map(simplify(config, state, ctx.neutral, _))
        val (bound_, re) = ctx.avoid(bound)
        val ctx_ = ctx.neutral.bind(bound_).assume(invariants(ctx, deps_, bound_), Nil)
        val body_ = simplify(config, state, ctx_, re(body))
        invs(config, state, ctx, deps_, bound_, body_)

  // the bodies of the invariants among the assumptions whose dependencies are among `deps`,
  // with their bound variables renamed to those of the corresponding dependencies in `bound`,
  // which hold at each position of the dependencies, hence also for the values bound there;
  // the dependencies of a combinator have equal length, such that the positions coincide
  def invariants(ctx: Ctx, deps: List[Expr], bound: List[Var]): List[Expr] =
    for
      case Invs(deps_, bound_, body) <- ctx.assms
      if deps_.forall(deps.contains)
    yield
      val re = Subst.from(bound_, deps_.map(dep => bound(deps.indexOf(dep))))
      re(body)

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

  // variables known to be equal to another one or to a literal are replaced
  def var_(config: Config, state: State, ctx: Ctx, x: Var): Expr =
    ctx.su.get(x) match
      case Some(y) => y
      case None    => x

  def eq_(config: Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case _ if left == right =>
        True

      case (x: Var, e) if point(ctx, x, e) =>
        True

      case (e, x: Var) if point(ctx, x, e) =>
        True

      case (Lit(a, _), Lit(b, _)) =>
        if a == b then True else False

      case (True, False) | (False, True) =>
        False

      case (_, True) => left
      case (True, _) => right
      case (_, False) => not(config, state, ctx, left)
      case (False, _) => not(config, state, ctx, right)

      case _ =>
        Eq(left, right)

  // one-point rule: forall x. C[x == e] is C[true] if x == e occurs negatively in C, and exists x. C[x == e] likewise
  // if it occurs positively, i.e., x is existential seen from the current position (see Ctx.flip),
  // which neutral positions forget, provided that x does not occur elsewhere, i.e., neither in e nor in the context,
  // and e does not depend on variables bound inside the scope of x, otherwise x cannot be instantiated by e,
  // e.g. not in forall x. exists y. !(x == y)
  def point(ctx: Ctx, x: Var, e: Expr): Boolean =
    (ctx.existential contains x)
      && !(e.free contains x)
      && !(Ctx.primed(e) contains x)
      && !(ctx.used contains x)
      && (e.free intersect ctx.bound.takeWhile(_ != x).toSet).isEmpty

  // equivalences are equations on Bool, the normal form, such that both are known from the context alike,
  // and as which SMT-LIB writes them
  def eqv(config: Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    eq_(config, state, ctx, left, right)

  // false if two of the expressions are equal, true if all of them are pairwise different,
  // e.g. literals, two expressions are distinct exactly if they are not equal
  def distinct(config: Config, state: State, ctx: Ctx, exprs: List[Expr]): Expr =
    val eqs = for case a :: rest <- exprs.tails.toList; b <- rest yield eq_(config, state, ctx.neutral, a, b)

    if eqs contains True
    then False
    else if eqs forall (_ == False)
    then True
    else
      exprs match
        case List(a, b) => not(config, state, ctx, Eq(a, b))
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
      case (_, False, True)      => not(config, state, ctx, test)
      case _                     => Ite(test, left, right)

  // read over write
  def select(config: Config, state: State, ctx: Ctx, base: Expr, index: Expr): Expr =
    base match
      case Store(_, index_, value) if index_ == index =>
        value

      case Store(base_, index_, _) if eq_(config, state, ctx.neutral, index_, index) == False =>
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

  // negated comparisons are the other comparison with the arguments swapped, !(a < b) is b <= a
  def not(config: Config, state: State, ctx: Ctx, phi: Expr): Expr =
    phi match
      case True             => False
      case False            => True
      case Not(psi)         => psi
      case Lt.int(a, b)     => Le.int(b, a)
      case Le.int(a, b)     => Lt.int(b, a)
      case Lt.real(a, b)    => Le.real(b, a)
      case Le.real(a, b)    => Lt.real(b, a)
      case _                => Not(phi)

  def imp(config: Config, state: State, ctx: Ctx, phi: Expr, psi: Expr): Expr =
    (phi, psi) match
      case (True, _)          => psi
      case (False, _)         => True
      case (_, True)          => True
      case (_, False)         => not(config, state, ctx, phi)
      case _ if phi == psi    => True
      case _                  => Imp(phi, psi)

  // flatten nested conjunctions, drop true and duplicates, false makes the whole conjunction false;
  // complementary pairs are decided already, since each conjunct is simplified assuming the others (see nary);
  // disjuncts common to all conjuncts are extracted, e.g. (A or C) and (A or B) is A or (C and B)
  def and(config: Config, state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.conjuncts
    if phis_.contains(False)
    then False
    else
      val (common, rests) = factor(phis_.map(phi => List(phi).disjuncts))
      if phis_.length < 2 || common.isEmpty
      then And(phis_)
      else or(config, state, ctx, common :+ and(config, state, ctx, rests.map(Or(_))))

  // dual to and
  def or(config: Config, state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.disjuncts
    if phis_.contains(True)
    then True
    else
      val (common, rests) = factor(phis_.map(phi => List(phi).conjuncts))
      if phis_.length < 2 || common.isEmpty
      then Or(phis_)
      else and(config, state, ctx, common :+ or(config, state, ctx, rests.map(And(_))))

  // the elements common to all of `args`, in the order of the first one, and what remains of each
  def factor(args: List[List[Expr]]): (List[Expr], List[List[Expr]]) =
    val common = args.headOption.getOrElse(Nil).filter(phi => args.forall(_ contains phi))
    (common, args.map(_.filterNot(common.contains)))

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

      // equations are invariant if both sides change alike
      case Eq(left, right) if left.typ == Sort.real =>
        val left_ = diff(config, state, xs, left)
        val right_ = diff(config, state, xs, right)
        Eq(left_, right_)

      case And(phis) =>
        val phis_ = phis.map(diff(config, state, xs, _))
        And(phis_)

      case _ =>
        Diff(xs, expr)

  // the difference right - left of the sides of a comparison as a normalized polynomial,
  // whose sign is all that matters, hence with integral coefficients without a common divisor
  def difference(config: Config, state: State, ctx: Ctx, ring: Ring, left: Expr, right: Expr): Poly =
    val left_ = poly(config, state, ctx, ring, left)
    val right_ = poly(config, state, ctx, ring, right)
    (right_ - left_).normalize.primitive

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

  // equations 0 == p on Int or Real are constants if p is, otherwise they are re-arranged like comparisons,
  // the result is an equation as built by eq_, e.g. by the one-point rule
  def eq(config: Config, state: State, ctx: Ctx, ring: Ring, poly: Poly): Expr =
    if poly.monos.isEmpty
    then if poly.const.isZero then True else False
    else
      val (left, right) = poly.sides
      eq_(config, state, ctx, left.toExpr(ring), right.toExpr(ring))

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

  // forall distributes over and, where each conjunct binds the variables that it uses
  def all(config: Config, state: State, ctx: Ctx, bound: List[Var], body: Expr): Expr =
    body match
      case And(phis) => and(config, state, ctx, phis.map(bind(config, state, ctx, All.name, bound, _)))
      case _         => bind(config, state, ctx, All.name, bound, body)

  // exists distributes over or, where each disjunct binds the variables that it uses
  def ex(config: Config, state: State, ctx: Ctx, bound: List[Var], body: Expr): Expr =
    body match
      case Or(phis) => or(config, state, ctx, phis.map(bind(config, state, ctx, Ex.name, bound, _)))
      case _        => bind(config, state, ctx, Ex.name, bound, body)

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
    val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, updates.free - acc)
    Trace(init, deps_, acc, bound_, updates.map(_.map(re(_))))

  def maps(config: Config, state: State, ctx: Ctx, deps: List[Expr], bound: List[Var], updates: List[Upd]): Expr =
    val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, updates.free)
    Maps(deps_, bound_, updates.map(_.map(re(_))))

  // invariants distribute over conjunctions, where each part keeps the dependencies that it uses;
  // with a constant body: true holds trivially,
  // false holds exactly if there are no values, i.e., the dependencies, which have the same length, are empty
  def invs(config: Config, state: State, ctx: Ctx, deps: List[Expr], bound: List[Var], body: Expr): Expr =
    (deps, body) match
      case (_, And(phis))     => and(config, state, ctx, phis.map(invs(config, state, ctx, deps, bound, _)))
      case (_, True)          => True
      case (dep :: _, False)  => Eq(Seqs.len(dep), Zero.int)
      case _ =>
        val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, body.free)
        Invs(deps_, bound_, re(body))

  // the dependencies of a combinator, whose bound variables are `bound`, and of whose body `used` are the free variables:
  // equal dependencies are collapsed, whose bound variables are renamed to the first one by the substitution,
  // and those whose bound variables are not used are dropped, except counters, which keep the dependencies nonempty
  // (if there is none, the first dependency is kept)
  def deps(config: Config, state: State, ctx: Ctx, deps: List[Expr], bound: List[Var], used: Set[Var]): (List[Expr], List[Var], Subst[Nothing, Var]) =
    val (distinct, re) =
      (deps zip bound).foldLeft((List.empty[(Expr, Var)], Subst.empty[Nothing, Var])):
        case ((done, re), (dep, x)) =>
          done.find((dep_, x_) => x_.typ == x.typ && eq_(config, state, ctx.neutral, dep_, dep) == True) match
            case Some((_, x_)) => (done, re + (x -> x_))
            case None          => (done :+ (dep, x), re)

    val used_ = used.map(x => re.vars.getOrElse(x, x))
    val kept =
      distinct.filter:
        case (Butlast(Counter(_, _, _)) | Counter(_, _, _), _) => true
        case (_, x)                                           => used_ contains x

    val pairs = if kept.isEmpty then distinct.take(1) else kept
    (pairs.map(_._1), pairs.map(_._2), re)
