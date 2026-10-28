package cuvee.prove

import util.Name
import cuvee.Debug
import cuvee.Error
import cuvee.Config
import cuvee.sexpr
import cuvee.pipe.Transform
import cuvee.core._
import util.Rational
import util.disjoint
import util.intersects

// contextual simplification of formulas, where each subterm is simplified under the facts known to hold at its
// position, the traversal of the engine of -prove (see Prove): the context holds the facts in classes, linear
// constraints and as they are (see Context), the reads of the components of state traces are markers (see Views),
// programs are not simplified here (see Slice)
object Simplify:
  // `ctx` is an empty context, which provides the rewrite rules;
  // the antecedents of assertions are assumed in the context of their succedents during simplification;
  // rules whose results grow, e.g. f(x) = f(f(x)), may exhaust the stack before the bound on the steps of the context
  // is reached (see Rewrite.apply), which is reported in the same way
  def simplify(config: Config, state: State, ctx: Context, cmd: Cmd): Cmd =
    try
      cmd match
        case Assert(justify, params, phi, attrs) =>
          Assert(justify, params, apply(config, state, ctx.copy(polarity = Some(true)), Normalize(phi)), attrs)

        case DefineFun(fun, body, attrs) =>
          DefineFun(fun, simplify(config, state, ctx, body), attrs)

        case _ =>
          cmd
    catch
      case _: StackOverflowError if ctx.rules.nonEmpty =>
        Error.raise("rewriting does not terminate")

  // the outer loop for assertions, which are normalized into clauses (see Normalize) before and after each round,
  // since simplification may produce nested implications and negations again,
  // and which are simplified again as long as they change, e.g. the equations of let are then known in the context;
  // normalizing before simplification removes let at positions with a polarity, whose body is neutral otherwise
  def apply(config: Config, state: State, ctx: Context, phi: Expr): Expr =
    val phi_ = Normalize(simplify(config, state, ctx, phi))
    if phi_ == phi
    then phi
    else apply(config, state, ctx, phi_)

  // each of `exprs` on its own in the same context, e.g. the arguments of a function
  def simplify(config: Config, state: State, ctx: Context, exprs: List[Expr]): List[Expr] =
    exprs.map(simplify(config, state, ctx, _))

  // simplify `expr` assuming that all facts in `ctx` hold
  // by repeated rounds of simplification until a fixpoint is reached,
  // a formula that is known from the context is replaced by its truth value (only formulas, which not applies to);
  // after each round, a rewrite rule of the context is applied at the top, whose subterms are simplified already, and a
  // term with a literal in its class is that literal
  // an expression in an inconsistent context is unreachable, any value is right there, and it stays as it is, since
  // every side condition holds and the rules would apply without end, e.g. to the reads of the history of a trace in
  // the dead branch of a decided test (swap.dfy); formulas are decided by their polarity first (see implied)
  def simplify(config: Config, state: State, ctx: Context, expr: Expr): Expr =
    decide(config, state, ctx, expr) match
      case Some(true)  => True
      case Some(false) => False
      case None =>
        val once_ = once(config, state, ctx, expr)
        if once_ != expr
        then Debug.step("simplify", show(config.output.printer, expr), show(config.output.printer, once_))

        // a term with a literal in its class is that literal (see Classes.ground)
        val expr_ = ctx.classes.ground(atom(rewrite(config, state, ctx, once_)))
        if expr_ == expr
        then forward(config, state, ctx, expr)
        else simplify(config, state, ctx, expr_)

  // an atom whose terms contain a choice as a value, e.g. the read earlier(j, maps(...)) of a map whose update has
  // cases, is the conjunction of the guards implying the atom at the results (see Normalize.choices), which keeps the
  // cases as guards of formulas; a choice that is itself the formula, the update of a trace of Bool, stays, and so does
  // a choice inside a list or a trace, the value of all its elements, e.g. consts(n, eps(...)) for guards that do not
  // depend on the iteration (maps_const), whose equation defines a trace in the classes
  // (atoms only: connectives are simplified part by part, whose atoms are lifted there)
  def atom(expr: Expr): Expr =
    expr match
      case And(_) | Or(_) | Not(_) | Imp(_, _)                    => expr
      case App(_, _, _, args) if expr.typ == Sort.bool && args.exists(value) => Normalize.choices(expr)
      case _                                                      => expr

  // whether a term contains a choice that is not inside a list or a trace
  def value(expr: Expr): Boolean =
    expr match
      case Eps(_)                                                                => true
      case App(_, _, Sort(Con.list | Con.trace, _), _)                           => false
      case App(_, _, _, args)                                                    => args.exists(value)
      case _                                                                     => false

  // a comparison or an equation at a position with a polarity, decided by the forward lemmas that fire on its own terms
  // (see Forward): at a positive position, it holds if its denial contradicts their instances, e.g. the bare goal
  // 0 <= (x + x * x) / 2 by the instance of triangle_nonneg at its term, and dually at a negative one; the instances
  // are not kept, since the atom is decided or stays as it is; the other formulas fire at the facts that the traversal
  // assumes (see Imp and nary)
  def forward(config: Config, state: State, ctx: Context, phi: Expr): Expr =
    phi match
      case App(fun, _, _, _) if ctx.forward.nonEmpty && Set("<", "<=", "=").contains(fun.name.name) && phi.typ == Sort.bool =>
        ctx.polarity match
          case Some(true) if Forward.assume(config, state, ctx, Nil, List(phi)).inconsistent  => True
          case Some(false) if Forward.assume(config, state, ctx, List(phi), Nil).inconsistent => False
          case _                                                                             => phi
      case _ =>
        phi

  // the decision of a formula by the theories of the context: true if implied, false if denied, and nothing for
  // terms that are no formulas (see implied, denied); the side conditions of rules are decided by simplification with
  // the rules (Rewrite.holds) and looked up among the facts (Rewrite.known)
  def decide(config: Config, state: State, ctx: Context, phi: Expr): Option[Boolean] =
    if implied(config, state, ctx, phi) then Some(true)
    else if denied(config, state, ctx, phi) then Some(false)
    else None

  // whether `phi` is known to hold in `ctx`, also by its negation in normal form, e.g. a < b if !(b <= a) is known
  // (see Context.implied), and in an inconsistent context at positive positions,
  // where any formula may be chosen (polarity is only defined for formulas); false for expressions that are no formulas
  def implied(config: Config, state: State, ctx: Context, phi: Expr): Boolean =
    phi.typ == Sort.bool && (phi == True
      || (ctx.inconsistent && ctx.polarity == Some(true))
      || ctx.implied(phi))

  // whether `phi` is known not to hold in `ctx`, dually, e.g. a < b if b <= a is known
  def denied(config: Config, state: State, ctx: Context, phi: Expr): Boolean =
    phi.typ == Sort.bool && (phi == False
      || (ctx.inconsistent && ctx.polarity == Some(false))
      || ctx.denied(phi))

  // expressions in debug output, on a single line
  def show(printer: cuvee.pipe.Printer, expr: Expr): String =
    printer.lines(expr).map(_.trim).mkString(" ")

  // rules in debug output, as the formula forall vars. cond ==> lhs == rhs on a single line
  def show(printer: cuvee.pipe.Printer, rule: Rule): String =
    val Rule(_, vars, lhs, rhs, cond, _) = rule
    val eq = if rhs == True then lhs else if rhs == False then Not(lhs) else Eq(lhs, rhs)
    show(printer, All(vars.toList, if cond == True then eq else Imp(cond, eq)))

  // a single step with the rewrite rules of the context at the top of `expr`,
  // where the conditions of the rules are decided by simplification in the context (see Rewrite)
  def rewrite(config: Config, state: State, ctx: Context, expr: Expr, self: Option[Var] = None): Expr =
    Rewrite.rewrite(config, state, ctx, expr, self)

  // a single round of simplification, dispatching on the builtin functions,
  // subterms are simplified first, where ite and the boolean connectives
  // extend the context by the facts known at the position of each subterm,
  // negation and the premise of implication flip the polarity,
  // and the arguments of other functions have none
  def once(config: Config, state: State, ctx: Context, expr: Expr): Expr =
    expr match
      case x: Var =>
        var_(config, state, ctx, x)

      case _: Lit | True | False =>
        expr

      // equations on Int and Real are compared as polynomials, like < and <=
      case Eq(left, right) if left.typ == Sort.int =>
        val poly_ = difference(config, state, ctx.neutral, Ints.ring, left, right)
        eq(config, state, ctx, Ints.ring, poly_)

      case Eq(left, right) if left.typ == Sort.real =>
        val poly_ = difference(config, state, ctx.neutral, Reals.ring, left, right)
        eq(config, state, ctx, Reals.ring, poly_)

      // the equation of a trace, X == trace(...), whose accumulator is the value of ⌊X⌋ in each iteration,
      // and of a map, Y == maps(...), whose update is the value of Y at each position, such that the update
      // assumes also the invariants of the context that mention ⌊X⌋ or Y (see invariants), e.g. the test of a loop;
      // the right-hand side is simplified like the combinator below, and then rewritten at the top (see simplify)
      // the histories of the accumulators denote them in the results (see Views.selfOf); the trace is rewritten at the
      // top with the variable as its self, also with several accumulators, whose histories then denote them in the
      // matcher as well (a lemma over a whole cycle, see Rewrite.matches_); without iterations, like the combinator below
      case Eq(x: Var, Trace(inits, deps, accs, bound, results)) =>
        val left_ = simplify(config, state, ctx.neutral, x)
        val inits_ = simplify(config, state, ctx.neutral, inits)
        val deps_ = simplify(config, state, ctx.neutral, deps)
        update(config, state, ctx, Some(x), inits_, deps_, accs, bound, results) match
          case None =>
            eq_(config, state, ctx, left_, Traces.stop(inits_.head))

          case Some((accs_, bound_, results_)) =>
            val right_ = trace(config, state, ctx.neutral, inits_, deps_, accs_, bound_, results_)
            eq_(config, state, ctx, left_, rewrite(config, state, ctx.neutral, right_, Some(x)))

      case Eq(y: Var, Maps(deps, bound, update)) =>
        val left_ = simplify(config, state, ctx.neutral, y)
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val inner = combinator(config, state, ctx.copy(self = List((y, re(update)))), deps_, bound_)
        if inner.inconsistent
        then eq_(config, state, ctx, left_, Lists.nil(update.typ))
        else
          val right_ = maps(config, state, ctx.neutral, deps_, bound_, simplify(config, state, inner, re(update)))
          eq_(config, state, ctx, left_, rewrite(config, state, ctx.neutral, right_, Some(y)))

      case Eq(left, right) =>
        val left_ = simplify(config, state, ctx.neutral, left)
        val right_ = simplify(config, state, ctx.neutral, right)
        eq_(config, state, ctx, left_, right_)

      case Eqv(left, right) =>
        val left_ = simplify(config, state, ctx.neutral, left)
        val right_ = simplify(config, state, ctx.neutral, right)
        eqv(config, state, ctx, left_, right_)

      case Distinct(exprs) =>
        val exprs_ = simplify(config, state, ctx.neutral, exprs)
        distinct(config, state, ctx, exprs_)

      case Is(arg, fun) =>
        val arg_ = simplify(config, state, ctx.neutral, arg)
        is(config, state, ctx, arg_, fun)

      // a derivative depends on the term, not only on its value: the body is simplified with the facts that do not
      // mention the variables xs only, e.g. x' == v at the head of an ode must not write v of (t, x, v :: v == a * t)'
      // as x', whose derivative would be 0
      case Diff(xs, arg) =>
        val arg_ = simplify(config, state, ctx.restricted(phi => xs disjoint phi.free).neutral, arg)
        diff(config, state, xs, arg_)

      case Old(arg) =>
        Old(simplify(config, state, ctx.neutral, arg))

      // the facts hold now, not at the other states of the trace that the operands of temporal operators talk about
      case Prop(op, args) =>
        Prop(op, simplify(config, state, ctx.restricted(_ => false).neutral, args))

      case As(arg, typ) =>
        val arg_ = simplify(config, state, ctx, arg)
        As(arg_, typ)

      // the branches have no polarity, since the context does not record the other branch (see Context.neutral);
      // a branch whose context is inconsistent is unreachable and dropped, also when the test itself is not decided
      case Ite(test, left, right) =>
        val test_ = simplify(config, state, ctx.neutral, test)
        val then_ = ctx.neutral.assume(List(test_), Nil)
        // the negated test, which may be stronger in the context, e.g. a strict comparison (see not)
        val else_ = ctx.neutral.assume(List(not(config, state, ctx, test_)), Nil)
        if then_.inconsistent then simplify(config, state, else_, right)
        else if else_.inconsistent then simplify(config, state, then_, left)
        else ite(config, state, ctx, test_, simplify(config, state, then_, left), simplify(config, state, else_, right))

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
        val phi_ = simplify(config, state, Forward.assume(config, state, ctx.flip, Nil, List(psi)), phi)
        val psi_ = simplify(config, state, Forward.assume(config, state, ctx, List(phi_), Nil), psi)
        imp(config, state, ctx, phi_, psi_)

      case And(phis) =>
        val phis_ = nary(config, state, ctx, Nil, phis, true)
        and(config, state, ctx, phis_)

      case Or(phis) =>
        val phis_ = nary(config, state, ctx, Nil, phis, false)
        or(config, state, ctx, phis_)

      case Ints.uminus(_) | Ints.plus(_) | Ints.minus(_, _) | Ints.times(_) =>
        arith(config, state, ctx.neutral, expr)

      // on Real, division by a nonzero literal is part of the polynomials
      case Reals.uminus(_) | Reals.plus(_) | Reals.minus(_, _) | Reals.times(_) | Reals.div(_, _) =>
        arith(config, state, ctx.neutral, expr)

      case Ints.div(left, right) =>
        val left_ = arith(config, state, ctx.neutral, left)
        val right_ = arith(config, state, ctx.neutral, right)
        div(config, state, ctx, left_, right_)

      case Ints.mod(left, right) =>
        val left_ = arith(config, state, ctx.neutral, left)
        val right_ = arith(config, state, ctx.neutral, right)
        mod(config, state, ctx, left_, right_)

      case Ints.lt(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Ints.ring, left, right)
        lt(config, state, ctx, Ints.ring, Ints.lt, poly_)

      case Reals.lt(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Reals.ring, left, right)
        lt(config, state, ctx, Reals.ring, Reals.lt, poly_)

      case Ints.le(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Ints.ring, left, right)
        le(config, state, ctx, Ints.ring, Ints.le, poly_)

      case Reals.le(left, right) =>
        val poly_ = difference(config, state, ctx.neutral, Reals.ring, left, right)
        le(config, state, ctx, Reals.ring, Reals.le, poly_)

      case Ints.gt(left, right) =>
        Ints.lt(right, left)

      case Reals.gt(left, right) =>
        Reals.lt(right, left)

      case Ints.ge(left, right) =>
        Ints.le(right, left)

      case Reals.ge(left, right) =>
        Reals.le(right, left)

      case Earlier(j, arg) =>
        val j_ = simplify(config, state, ctx, j)
        val arg_ = simplify(config, state, ctx, arg)
        earlier(config, state, ctx, j_, arg_)

      case App(fun, inst, typ, args) =>
        val args_ = simplify(config, state, ctx.neutral, args)
        app(config, state, ctx, fun, inst, typ, args_)

      // bound variables are renamed apart from the context before entering the body
      case All(bound, body) =>
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val body_ = simplify(config, state, ctx.forall(bound_), re(body))
        all(config, state, ctx, bound_, body_)

      case Ex(bound, body) =>
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val body_ = simplify(config, state, ctx.exists(bound_), re(body))
        ex(config, state, ctx, bound_, body_)

      // the body has no polarity, since the context does not record the bindings
      case Let(bound, args, body) =>
        val args_ = simplify(config, state, ctx.neutral, args)
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val body_ = simplify(config, state, ctx.neutral.bind(bound_), re(body))
        let(config, state, ctx, bound_, args_, body_)

      // the body has no polarity, like that of let
      case Lam(bound, body, typ) =>
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val body_ = simplify(config, state, ctx.neutral.bind(bound_), re(body))
        lam(config, state, ctx, bound_, body_, typ)

      case Match(arg, cases) =>
        val arg_ = simplify(config, state, ctx.neutral, arg)
        match_(config, state, ctx, arg_, cases.flatMap(this.cases(config, state, ctx, _)))

      // the cases like those of match, the function is not unfolded
      case Rec(fun, cases) =>
        rec(config, state, ctx, fun, cases.flatMap(this.cases(config, state, ctx, _)))

      // the combinators bind the accumulator and the variables for the dependencies like quantifiers,
      // their updates and bodies assume the invariants of the context over the same dependencies (see combinator)
      // a projection of a trace of several accumulators has the history of its component as self (see Views.relation);
      // the histories ⌊S⌋.j among the dependencies are inert (see Views);
      // a combinator whose inner context is inconsistent has no iterations: a trace stops at its initial value,
      // a map is nil, invariants hold
      case Trace(inits, deps, accs, bound, results) =>
        val inits_ = simplify(config, state, ctx.neutral, inits)
        val deps_ = simplify(config, state, ctx.neutral, deps)
        update(config, state, ctx, None, inits_, deps_, accs, bound, results) match
          case None                            => Traces.stop(inits_.head)
          case Some((accs_, bound_, results_)) => trace(config, state, ctx, inits_, deps_, accs_, bound_, results_)

      // the reads of the components of a trace of several accumulators are markers, replaced by their views once these
      // read no component any more (see Views), e.g. the counter of a loop by its value; otherwise they stay, and the
      // matcher matches them modulo their views (see Rewrite.matchesExpr)
      case Component(s, i) =>
        view(config, state, ctx, s, Component(simplify(config, state, ctx.neutral, s), i))

      case History(s, i) =>
        view(config, state, ctx, s, History(simplify(config, state, ctx.neutral, s), i))

      case Maps(deps, bound, update) =>
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val inner = combinator(config, state, ctx, deps_, bound_)
        if inner.inconsistent
        then Lists.nil(update.typ)
        else maps(config, state, ctx, deps_, bound_, simplify(config, state, inner, re(update)))

      // the guards of the cases are simplified, cases whose guard is false are dropped,
      // and the results are simplified assuming their guard and, since the guards are disjoint, that the others are false;
      // not so the guards themselves, which could become weaker and overlap, e.g. both true for complementary guards;
      // a case whose context is inconsistent is unreachable and dropped
      case Eps(updates) =>
        val updates_ =
          for
            Upd(cond, rhs) <- updates
            cond_ = simplify(config, state, ctx.neutral, cond)
            if cond_ != False
          yield Upd(cond_, rhs)

        val updates__ =
          for
            (Upd(cond_, rhs), i) <- updates_.zipWithIndex
            inner = ctx.neutral.assume(List(cond_), updates_.guards.patch(i, Nil, 1))
            if !inner.inconsistent
          yield upd(config, state, ctx, cond_, simplify(config, state, inner, rhs))

        eps(config, state, ctx, expr.typ, updates__)

      // the body holds for all values of the dependencies, like the body of a universal quantifier,
      // but without polarity, since the dependencies are not recorded in the context
      case Invs(deps, bound, body) =>
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val inner = combinator(config, state, ctx, deps_, bound_)
        if inner.inconsistent
        then True
        else invs(config, state, ctx, deps_, bound_, simplify(config, state, inner, re(body)))

  // the results of a trace simplified in the context of its update (see combinator), with the accumulators and the
  // bound variables renamed apart from the context, and the self of the position (see Views.self), which `self`
  // defines if given; the update of a single accumulator assumes the range of its remainders (see wrapped); none if
  // the context of the update of a single accumulator is inconsistent, i.e., the trace has no iterations
  def update(
      config: Config,
      state: State,
      ctx: Context,
      self: Option[Var],
      inits: List[Expr],
      deps: List[Expr],
      accs: List[Var],
      bound: List[Var],
      results: List[Expr]
  ): Option[(List[Var], List[Var], List[Expr])] =
    val (vars_, re) = Subst.rename(accs ++ bound, ctx.free)
    val (accs_, bound_) = vars_.splitAt(accs.length)
    val inner = combinator(config, state, ctx.bind(accs_).copy(self = Views.self(ctx, self, deps, accs_)), deps, bound_)
    val ranges = if accs.length == 1 then wrapped(config, state, ctx, inner, inits.head, accs_.head, re(results.head)) else Nil
    val inner_ = inner.assume(ranges, Nil)
    if inner_.inconsistent && accs.length == 1
    then None
    else Some((accs_, bound_, results.map(result => simplify(config, state, inner_, re(result)))))

  // a read of a component of the trace `s`, replaced by its view once that reads no component any more (see Views)
  def view(config: Config, state: State, ctx: Context, s: Expr, expr: Expr): Expr =
    Views.projected(config, state, ctx, expr) match
      case Some(e) if Views.closed(Views.traceOf(ctx, s).map(_._1).getOrElse(s), e) => e
      case _                                                                          => expr

  // the context of the updates and bodies of combinators, which binds the variables for the dependencies,
  // and which assumes the invariants of the context over the same dependencies and the iterations of loops;
  // ctx.self is the dependency that the combinator defines and its value in the update, if known (see once)
  // built once per command for the same outer context (see Context.memo)
  // the facts of the context are memoized under the canonical names of the position (see Canon), such that positions
  // that differ only by the names of their bound variables share them; the context is built from them at each
  // position, which keeps the suspended rules and components of the position
  def combinator(config: Config, state: State, ctx: Context, deps: List[Expr], bound: List[Var]): Context =
    val facts = ctx.memo("combinator", deps, bound)(invariants(ctx, deps, bound) ++ iterations(config, state, ctx, deps, bound))
    ctx.neutral.bind(bound).assume(facts, Nil)

  // the range 0 <= acc < k of the accumulator of a trace whose initial value is known to be in it and whose results are
  // remainders modulo k or the accumulator itself, which holds for all values of the accumulator by induction, e.g. of
  // an unsigned variable of C, x == trace(0, for ... do x, ... :: (x + 1) % 4294967296); under the test of the loop,
  // e.g. x < 100, the remainder in the update is then the sum itself (see mod); the results are simplified in the context
  // `inner` of the update first, which unfolds the overflow functions of C, e.g. uint(x + 1) to (x + 1) % 4294967296
  def wrapped(config: Config, state: State, ctx: Context, inner: Context, init: Expr, acc: Var, update: Expr): List[Expr] =
    def results(expr: Expr): List[Expr] =
      expr match
        case Eps(updates)       => Eps.flatten(updates).flatMap(upd => results(upd.rhs))
        case Ite(_, left, right) => results(left) ++ results(right)
        case _                  => List(expr)

    val results_ = results(update).map(simplify(config, state, inner, _))
    val moduli = results_.collect { case Ints.mod(_, Lit(k: BigInt, _)) if k != 0 => k.abs }.distinct
    val bounded = results_.forall:
      case Ints.mod(_, Lit(k: BigInt, _)) => moduli == List(k.abs)
      case result                         => result == acc

    moduli match
      case List(k) if bounded =>
        val range = (e: Expr) => List(Ints.le(Ints.zero, e), Ints.lt(e, Lit(k, Sort.int)))
        if simplify(config, state, ctx.neutral, And(range(init))) == True
        then range(acc)
        else Nil

      case _ =>
        Nil

  // the bodies of the invariants among the assumptions whose dependencies are among `deps` and `self`,
  // with their bound variables renamed to those of the corresponding dependencies in `bound`, or to the value of ctx.self,
  // which hold at each position of the dependencies, hence also for the values bound there;
  // the dependencies of a combinator have equal length, such that the positions coincide
  // the self of the context maps further dependencies to their values in the update: ⌊X⌋ to the accumulator of X, the
  // histories ⌊S⌋.j to the accumulators of a trace of several, the history of the own component of a projection to
  // its accumulator (see Views.selfOf and Views.relation), such that e.g. the test lo < hi of a loop bounds the
  // accumulator of the projection of lo
  def invariants(ctx: Context, deps: List[Expr], bound: List[Var]): List[Expr] =
    val values = (deps zip bound).toMap[Expr, Expr] ++ ctx.self
    for
      case Invs(deps_, bound_, body) <- ctx.facts.assms
      if deps_.forall(values.contains)
    yield
      val re = Subst.from(bound_, deps_.map(values))
      re(body)

  // if the first dependency counts the iterations of a loop, ⌊counter(0, 1, n)⌋ bound to k (see Rewrite.counter),
  // then 0 <= k < n, since the loop exits when k == n, and the variable z bound to each other dependency ⌊Z⌋
  // is its value in iteration k, i.e., z == earlier(k, ⌊Z⌋), which is simplified within the range,
  // e.g. z == k for ⌊Z⌋ with Z == counter(0, 1, n), which then bounds z as well
  // the reads are normalized by the rules without an invs side condition only (see Rule.plain): a summary whose
  // condition is matched against the invs facts would build the contexts of those facts in turn, whose reads are
  // normalized again, through every such rule, which exhausts the steps (see Context.active)
  def iterations(config: Config, state: State, ctx: Context, deps: List[Expr], bound: List[Var]): List[Expr] =
    ctx.memo("reads", deps, bound):
      (deps, bound, deps.headOption.flatMap(Rewrite.counter(ctx, _))) match
        case (_ :: deps_, k :: bound_, Some(n)) =>
          val ctx_ = ctx.neutral.bind(bound).copy(rules = ctx.rules.filter(Rule.plain))
          val bounds = List(Ints.le(Ints.zero, k), Ints.lt(k, n))
          val range = simplify(config, state, ctx_, bounds)
          val inside = ctx_.assume(range, Nil)
          range ++ (deps_ zip bound_).map((dep, z) => Eq(z, simplify(config, state, inside, Earlier(k, dep))))

        case _ =>
          Nil

  // the variables of the pattern are renamed apart like bound variables, and the body assumes the condition,
  // without polarity, since the context does not record the argument;
  // a case whose guard contradicts the context is unreachable and dropped
  def cases(config: Config, state: State, ctx: Context, cs: Case): Option[Case] =
    val Case(pat, body, cond) = cs
    val (bound_, re) = Subst.rename(pat.free.toList, ctx.free)
    val cond_ = simplify(config, state, ctx.neutral.bind(bound_), re(cond))
    val inner = ctx.neutral.bind(bound_).assume(List(cond_), Nil)
    if inner.inconsistent then None
    else Some(case_(config, state, ctx, re(pat), simplify(config, state, inner, re(body)), cond_))

  // simplify each of `phis` assuming the others, which hold if `pos` (conjunction)
  // and do not hold otherwise (disjunction);
  // propositions in `done` are already processed (in reverse) and assumed in their simplified form,
  // otherwise e.g. both copies in `a and a` would simplify to true
  def nary(config: Config, state: State, ctx: Context, done: List[Expr], phis: List[Expr], pos: Boolean): List[Expr] =
    phis match
      case Nil =>
        done.reverse

      case phi :: rest =>
        val others = done ++ rest
        val ctx_ =
          if pos
          then Forward.assume(config, state, ctx, others, Nil)
          else Forward.assume(config, state, ctx, Nil, others)
        val phi_ = simplify(config, state, ctx_, phi)
        nary(config, state, ctx, phi_ :: done, rest, pos)

  // simplify an integer- or real-valued term into the normal form of polynomials,
  // terms of other types, e.g. of defined sorts, are simplified only
  def arith(config: Config, state: State, ctx: Context, expr: Expr): Expr =
    Ring(expr.typ) match
      case Some(ring) => poly(config, state, ctx, ring, expr).normalize.toExpr(ring)
      case None       => simplify(config, state, ctx, expr)

  // an integer- or real-valued term as a polynomial (not normalized), its leaves simplified (see Arith.toPoly), the
  // solved variables among them replaced by their solutions (see Classes.substitute)
  def poly(config: Config, state: State, ctx: Context, ring: Ring, expr: Expr): Poly =
    Arith.toPoly(ring, expr, leaf(config, state, ctx, _))

  // a leaf of arithmetic simplified, as its solution if it has one (see Classes.value)
  def leaf(config: Config, state: State, ctx: Context, expr: Expr): Expr =
    ctx.classes.value(simplify(config, state, ctx, expr))

  // a variable is replaced by the root of its class (see Classes.normalize): its literal, or the variable of the
  // outermost scope (see Classes.Order); its solution only inside arithmetic (see poly), while the matcher still tries
  // every member of the class
  def var_(config: Config, state: State, ctx: Context, x: Var): Expr =
    ctx.classes.term(x)

  def eq_(config: Config, state: State, ctx: Context, left: Expr, right: Expr): Expr =
    (left, right) match
      case _ if left == right =>
        True

      // variables with the same definition among the assumptions, or a variable and its definition (see Context.↑)
      case (ctx.↑(left_), ctx.↑(right_)) if left_ == right_ =>
        True

      // terms known to be equal by the classes, and terms with binders that are equal modulo the names of their bound
      // variables and the orders that do not matter (see Canon.equal), e.g. two cases of a choice with equal results
      // that bind their variables differently, or two dependencies of a combinator
      case _ if ctx.classes.equal(left, right) || Canon.equal(left, right) =>
        True

      case (x: Var, e) if point(ctx, x, e) =>
        True

      case (e, x: Var) if point(ctx, x, e) =>
        True

      case (Lit(a, _), Lit(b, _)) =>
        if a == b then True else False

      case (True, False) | (False, True) =>
        False

      case (_, True)  => left
      case (True, _)  => right
      case (_, False) => not(config, state, ctx, left)
      case (False, _) => not(config, state, ctx, right)

      // a conditional is lifted over the equation, whose branches are then decided under the test, e.g. ite(c, 1, 0) == 0
      // of assume_abort_if_not in C is !c, and (if x != c then x else d) != c is true for c != d
      case (Ite(test, a, b), d) =>
        ite(config, state, ctx, test, eq_(config, state, ctx, a, d), eq_(config, state, ctx, b, d))

      case (d, Ite(test, a, b)) =>
        ite(config, state, ctx, test, eq_(config, state, ctx, d, a), eq_(config, state, ctx, d, b))

      // extensionality: lambdas are equal if their bodies are for all values of the variables, which are renamed apart,
      // the equation of an array or function value and a lambda is kept, which defines it (see select and app)
      case (Lam(xs, body, _), Lam(ys, body_, _)) if xs.length == ys.length =>
        val clash = (body.free -- xs) ++ (body_.free -- ys) ++ ctx.free
        val (zs, re) = Subst.rename(xs, clash)
        val eq = eq_(config, state, ctx.neutral.bind(zs), re(body), Subst.from(ys, zs)(body_))
        all(config, state, ctx, zs, eq)

      case _ =>
        Eq(left, right)

  // one-point rule: forall x. C[x == e] is C[true] if x == e occurs negatively in C, and exists x. C[x == e] likewise
  // if it occurs positively, i.e., x is existential seen from the current position (see Context.flip),
  // which neutral positions forget, provided that x does not occur elsewhere, i.e., neither in e nor in the context,
  // and e does not depend on variables bound inside the scope of x, otherwise x cannot be instantiated by e,
  // e.g. not in forall x. exists y. !(x == y)
  def point(ctx: Context, x: Var, e: Expr): Boolean =
    // the variables of the binders inside that of x, those of the binder of x are not nested
    val inner = ctx.bound.takeWhile(!_.contains(x)).flatten.toSet
    val existential = ctx.existential contains x
    val recursive = e.free contains x
    val used = ctx.used contains x
    val dependent = e.free intersects inner
    existential && !recursive && !used && !dependent

  // equivalences are equations on Bool, the normal form, such that both are known from the context alike,
  // and as which SMT-LIB writes them
  def eqv(config: Config, state: State, ctx: Context, left: Expr, right: Expr): Expr =
    eq_(config, state, ctx, left, right)

  // false if two of the expressions are equal, true if all of them are pairwise different,
  // e.g. literals, two expressions are distinct exactly if they are not equal
  def distinct(config: Config, state: State, ctx: Context, exprs: List[Expr]): Expr =
    val eqs = for case a :: rest <- exprs.tails.toList; b <- rest yield eq_(config, state, ctx.neutral, a, b)

    if eqs contains True
    then False
    else if eqs forall (_ == False)
    then True
    else
      exprs match
        case List(a, b) => not(config, state, ctx, Eq(a, b))
        case _          => Distinct(exprs)

  // testers on constructor applications, also of variables defined by one (see Context.↑),
  // which is looked up once only here, not in constr, since definitions through annotations may be cyclic
  def is(config: Config, state: State, ctx: Context, arg: Expr, fun: Fun): Expr =
    val constr_ =
      arg match
        case ctx.↑(arg_) => constr(config, state, arg_)
        case _           => None

    constr_ match
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

  def ite(config: Config, state: State, ctx: Context, test: Expr, left: Expr, right: Expr): Expr =
    (test, left, right) match
      case (True, _, _)       => left
      case (False, _, _)      => right
      case _ if left == right => left
      case (_, True, False)   => test
      case (_, False, True)   => not(config, state, ctx, test)
      case _                  => Ite(test, left, right)

  // read over write, also of arrays defined by a write (see Context.↑), and beta reduction of lambdas
  def select(config: Config, state: State, ctx: Context, base: Expr, index: Expr): Expr =
    base match
      case ctx.↑(Store(_, index_, value)) if index_ == index =>
        value

      case ctx.↑(Lam(List(x), body, _)) =>
        Subst.from(List(x), List(index))(body)

      case ctx.↑(Store(base_, index_, _)) if eq_(config, state, ctx.neutral, index_, index) == False =>
        Select(base_, index)

      // the indices decided by the facts, e.g. a[3 := w][j] with j != 3 known (single_elem_safe)
      case ctx.↑(Store(_, index_, value)) if ctx.neutral.implied(Eq(index_, index)) =>
        value

      case ctx.↑(Store(base_, index_, _)) if ctx.neutral.denied(Eq(index_, index)) =>
        Select(base_, index)

      case _ =>
        Select(base, index)

  def store(config: Config, state: State, ctx: Context, base: Expr, index: Expr, value: Expr): Expr =
    (base, value) match
      // overwritten, also arrays defined by a write (see Context.↑)
      case (ctx.↑(Store(base_, index_, _)), _) if index_ == index =>
        Store(base_, index, value)

      // writes back what is already stored
      case (_, Select(base_, index_)) if base_ == base && index_ == index =>
        base

      case _ =>
        Store(base, index, value)

  // the negation in normal form (see Context.not), strengthened in the context, for terms and for assumptions:
  // a disequation on Int is strict in the direction that the context bounds, e.g. k != 0 is 0 < k if 0 <= k
  def not(config: Config, state: State, ctx: Context, phi: Expr): Expr =
    phi match
      case Eq(a, b) if a.typ == Sort.int && implied(config, state, ctx.neutral, Ints.le(a, b)) => Ints.lt(a, b)
      case Eq(a, b) if a.typ == Sort.int && implied(config, state, ctx.neutral, Ints.le(b, a)) => Ints.lt(b, a)
      case _ => Context.not(phi)

  def imp(config: Config, state: State, ctx: Context, phi: Expr, psi: Expr): Expr =
    (phi, psi) match
      case (True, _)       => psi
      case (False, _)      => True
      case (_, True)       => True
      case (_, False)      => not(config, state, ctx, phi)
      case _ if phi == psi => True
      case _               => Imp(phi, psi)

  // flatten nested conjunctions, drop true and duplicates, false makes the whole conjunction false;
  // complementary pairs are decided already, since each conjunct is simplified assuming the others (see nary);
  // disjuncts common to all conjuncts are extracted, e.g. (A or C) and (A or B) is A or (C and B)
  def and(config: Config, state: State, ctx: Context, phis: List[Expr]): Expr =
    val phis_ = phis.conjuncts
    if phis_.contains(False)
    then False
    else
      val (common, rests) = factor(phis_.map(phi => List(phi).disjuncts))
      if phis_.length < 2 || common.isEmpty
      then And(phis_)
      else or(config, state, ctx, common :+ and(config, state, ctx, rests.map(Or(_))))

  // dual to and
  def or(config: Config, state: State, ctx: Context, phis: List[Expr]): Expr =
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
  def div(config: Config, state: State, ctx: Context, left: Expr, right: Expr): Expr =
    (left, right) match
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) if n != 0 =>
        val r = m mod n.abs
        Lit((m - r) / n, Sort.int)

      case (_, Lit(n: BigInt, _)) if n == 1 =>
        left

      // normalized in the next round
      case (_, Lit(n: BigInt, _)) if n == -1 =>
        Ints.uminus(left)

      // a polynomial whose coefficients are multiples of n, up to the constant c, is divided exactly,
      // (n * p + c) div n = p + c div n, e.g. 3 * x / 3 is x
      case (_, Lit(n: BigInt, _)) if n != 0 =>
        val poly = Arith.toPoly(Ints.ring, left).normalize
        if poly.monos.nonEmpty && poly.monos.forall(m => m.factor.den == 1 && m.factor.num % n == 0)
        then
          val c = poly.const.num
          Poly(Rational((c - (c mod n.abs)) / n), poly.monos.map(_ * Rational(1, n))).toExpr(Ints.ring)
        else Ints.div(left, right)

      case _ =>
        Ints.div(left, right)

  def mod(config: Config, state: State, ctx: Context, left: Expr, right: Expr): Expr =
    (left, right) match
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) if n != 0 =>
        Lit(m mod n.abs, Sort.int)

      case (_, Lit(n: BigInt, _)) if n == 1 || n == -1 =>
        Ints.zero

      // the coefficients and the constant of a polynomial are taken modulo n, e.g. (2 * x + 3) % 2 is 1, after its
      // remainders modulo multiples of n are replaced by their arguments, e.g. (x % 4294967296 + 1) % 4294967296 is
      // (x + 1) % 4294967296 and (x % 4294967296) % 2 is x % 2; the remainder is the polynomial itself if it is known to
      // be in the range 0, ..., n - 1, or a representative of it (see representatives); for a small n, the remainder of
      // p + c is that of p plus c, if the context fixes the remainder of p, e.g. (i + 1) % 2 is 1 where i % 2 == 0, the
      // parity of successors, which the rational simplex does not see (the case splits of Prove are on p % n as well)
      case (_, Lit(n: BigInt, _)) if n != 0 =>
        val poly = Arith.toPoly(Ints.ring, left)
        val reduced = remainders(ctx, n, poly).modulo(n)
        val base = (reduced - Poly.const(reduced.const)).normalize
        val known =
          if reduced.const.isZero || base.monos.isEmpty || n.abs > 4
          then None
          else
            val atom = Ints.mod(base.toExpr(Ints.ring), right)
            List.range(BigInt(0), n.abs).find(r => ctx.neutral.implied(Eq(atom, Lit(r, Sort.int))))
        (reduced != poly.normalize, known) match
          case (true, _) =>
            mod(config, state, ctx, reduced.toExpr(Ints.ring), right)

          case (false, Some(r)) =>
            Lit((r + reduced.const.num) mod n.abs, Sort.int)

          case (false, None) =>
            val inside =
              for
                poly_ <- representatives(n, reduced)
                expr = poly_.toExpr(Ints.ring)
                if simplify(config, state, ctx.neutral, And(List(Ints.le(Ints.zero, expr), Ints.lt(expr, Lit(n.abs, Sort.int))))) == True
              yield expr
            inside.headOption.getOrElse(Ints.mod(left, right))

      case _ =>
        Ints.mod(left, right)

  // `poly` with its atoms e % k replaced by e where n divides k, which is equal modulo n; also variables whose definition
  // in the context is such a remainder, e.g. the final value x of a loop with x == current(X) after rewriting, unless
  // the definition refers to the variable itself; and variables whose definition is a polynomial that is constant modulo
  // n, e.g. zz % 2 with zz == 2 * count(...), not those that only reduce to other atoms, which may be variables whose
  // definitions lead back (x == y + 2, y == x - 2)
  def remainders(ctx: Context, n: BigInt, poly: Poly): Poly =
    def atom(expr: Expr): Poly =
      (expr, expr) match
        case (x: Var, ctx.↑(Ints.mod(e, _))) if e.free contains x =>
          Poly.atom(expr)
        case (_, ctx.↑(Ints.mod(e, Lit(k: BigInt, _)))) if k != 0 && k % n == 0 =>
          Arith.toPoly(Ints.ring, e)
        case (x: Var, ctx.↑(e)) if x.typ == Sort.int =>
          val reduced = Arith.toPoly(Ints.ring, e).modulo(n)
          if reduced.monos.isEmpty then reduced else Poly.atom(expr)
        case _ =>
          Poly.atom(expr)

    val monos =
      for Mono(factor, atoms) <- poly.monos
      yield atoms.foldLeft(Poly.const(factor)) { case (product, (expr, exp)) =>
        List.fill(exp.toInt)(atom(expr)).foldLeft(product)(_ * _)
      }
    monos.foldLeft(Poly.const(poly.const))(_ + _)

  // the polynomials equal to `poly` modulo n that are candidates for the value of poly % n, the reduced one itself and the
  // one whose coefficients and constant are between -|n|/2 and |n|/2, e.g. x - 1 for x + 4294967295 modulo 4294967296,
  // which is the value of the remainder if 1 <= x
  def representatives(n: BigInt, poly: Poly): List[Poly] =
    def centered(r: Rational) =
      if r.num > n.abs / 2 then r - Rational(n.abs) else r
    val centered_ = Poly(centered(poly.const), poly.monos.map(m => Mono(centered(m.factor), m.atoms))).normalize
    List(poly, centered_).distinct

  // the derivative of `expr` with respect to `xs` (see Diff), by the rules of dL:
  // derivatives are on Real only, derivatives of terms on Int are kept;
  // terms that do not contain xs have derivative 0, a variable x in xs has derivative x',
  // derivatives are linear, products follow the product rule,
  // and the derivative of e < f and of e <= f is e' <= f', that of a conjunction is the conjunction of the derivatives;
  // derivatives of other expressions are kept, e.g. of applications of other functions and of division
  def diff(config: Config, state: State, xs: List[Var], expr: Expr): Expr =
    expr match
      case _ if expr.typ == Sort.real && (xs disjoint expr.free) =>
        Reals.zero

      case x: Var if x.typ == Sort.real =>
        x.primed

      case Reals.uminus(arg) =>
        val arg_ = diff(config, state, xs, arg)
        Reals.uminus(arg_)

      case Reals.plus(args) =>
        val args_ = args.map(diff(config, state, xs, _))
        Reals.plus(args_)

      case Reals.minus(left, right) =>
        val left_ = diff(config, state, xs, left)
        val right_ = diff(config, state, xs, right)
        Reals.minus(left_, right_)

      // (a * b * c)' = a' * b * c + a * b' * c + a * b * c'
      case Reals.times(args) =>
        val summands =
          for (arg, i) <- args.zipWithIndex
          yield
            val arg_ = diff(config, state, xs, arg)
            Reals.times(args.updated(i, arg_))
        Reals.plus(summands)

      case Reals.lt(left, right) =>
        val left_ = diff(config, state, xs, left)
        val right_ = diff(config, state, xs, right)
        Reals.le(left_, right_)

      case Reals.le(left, right) =>
        val left_ = diff(config, state, xs, left)
        val right_ = diff(config, state, xs, right)
        Reals.le(left_, right_)

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
  def difference(config: Config, state: State, ctx: Context, ring: Ring, left: Expr, right: Expr): Poly =
    Arith.difference(ring, left, right, leaf = leaf(config, state, ctx, _)).primitive

  // comparisons 0 < p and 0 <= p on Int or Real, built by `op`, are constants if p is,
  // otherwise they are re-arranged so that both sides have positive coefficients only,
  // e.g. 0 < y - x + 1 becomes x < y + 1
  // on Int, n < m + 1 is n <= m, and 0 < p is 0 < q + 1 where 0 <= q is 0 <= p - 1 rounded (see Poly.floor),
  // e.g. 2 * n < 52 is n < 26
  def lt(config: Config, state: State, ctx: Context, ring: Ring, op: Sugar.binary, poly: Poly): Expr =
    val tight = (poly - Poly.one).floor + Poly.one
    if poly.monos.isEmpty
    then if poly.const.isPositive then True else False
    else if ring == Ints.ring && tight != poly
    then lt(config, state, ctx, ring, op, tight)
    else
      val (left, right) = poly.sides
      (ring, right.toExpr(ring)) match
        case (Ints.ring, ctx.↑(Ints.succ(right_))) => Ints.le(left.toExpr(ring), right_)
        case (_, right_)                     => op(left.toExpr(ring), right_)

  // equations 0 == p on Int or Real are constants if p is, otherwise they are re-arranged like comparisons,
  // the result is an equation as built by eq_, e.g. by the one-point rule,
  // which applies also to a variable for which the equation can be solved, e.g. n + x == 40 for x (see Poly.solution)
  def eq(config: Config, state: State, ctx: Context, ring: Ring, poly: Poly): Expr =
    if poly.monos.isEmpty
    then if poly.const.isZero then True else False
    else if poly.solution(ctx.order.rank, (x, rest) => point(ctx, x, rest.toExpr(ring))).nonEmpty
    then True
    else
      val (left, right) = poly.sides
      eq_(config, state, ctx, left.toExpr(ring), right.toExpr(ring))

  // on Int, n + 1 <= m is n < m, 0 <= p is rounded (see Poly.floor), e.g. 2 * n + 1 <= 52 is n <= 25,
  // n <= m is n == m if m <= n is known, e.g. for 0 <= x <= 0, whose equation is then substituted,
  // and n < m if n != m is known (the decisions are neutral)
  def le(config: Config, state: State, ctx: Context, ring: Ring, op: Sugar.binary, poly: Poly): Expr =
    if poly.monos.isEmpty
    then if poly.const.isNegative then False else True
    else if ring == Ints.ring && poly.floor != poly
    then le(config, state, ctx, ring, op, poly.floor)
    else
      val (left, right) = poly.sides
      val (left_, right_) = (left.toExpr(ring), right.toExpr(ring))
      (ring, left_) match
        case (Ints.ring, ctx.↑(Ints.succ(left__))) =>
          Ints.lt(left__, right_)

        case (Ints.ring, _) if implied(config, state, ctx.neutral, Ints.le(right_, left_)) =>
          eq_(config, state, ctx, left_, right_)

        case (Ints.ring, _)
            if denied(config, state, ctx.neutral, Eq(left_, right_)) || denied(config, state, ctx.neutral, Eq(right_, left_)) =>
          Ints.lt(left_, right_)

        case _ =>
          op(left_, right_)

  // earlier moves inward: into maps, whose element j is its update for the elements j of the dependencies, a choice if
  // it has cases (see atom), into both branches of ite, and into the body of let, whose bound variables are renamed
  // apart from j
  def earlier(config: Config, state: State, ctx: Context, j: Expr, arg: Expr): Expr =
    (j, arg) match
      case (j, ctx.↑(Maps(deps, bound, update))) =>
        val su = Subst.from(bound, deps.map(earlier(config, state, ctx, j, _)))
        su(update)

      case (j, Ite(test, left, right)) =>
        ite(config, state, ctx, test, earlier(config, state, ctx, j, left), earlier(config, state, ctx, j, right))

      case (j, Let(bound, args, body)) =>
        val (bound_, re) = Subst.rename(bound, ctx.free ++ j.free)
        let(config, state, ctx, bound_, args, earlier(config, state, ctx.bind(bound_), j, re(body)))

      case _ =>
        Earlier(j, arg)

  // applications of other functions, e.g. user-defined ones, and beta reduction of function values,
  // also of those defined by a lambda (see Context.↑)
  def app(config: Config, state: State, ctx: Context, fun: Fun, inst: List[Type], typ: Type, args: List[Expr]): Expr =
    App(fun, inst, typ, args) match
      case Apply(ctx.↑(Lam(bound, body, _)), args_) if bound.length == args_.length =>
        Subst.from(bound, args_)(body)

      // the component of a constructor application is its argument, also of a term defined by one (see Context.↑)
      case expr @ App(sel, _, _, List(arg)) =>
        (selector(state, sel), arg) match
          case (Some((constr, i)), ctx.↑(App(fun, _, _, args))) if fun == constr => args(i)
          case _                                                                => expr

      case expr =>
        expr

  // the constructor whose selector `sel` is, and the position of the selector among its selectors, by the datatype of
  // the formal parameter of the selector, such that the lookup is cheap for the applications of other functions
  def selector(state: State, sel: Fun): Option[(Fun, Int)] =
    sel.formals match
      case List(Var(_, Sort(con, _))) =>
        state.datatypes.get(con.name).flatMap: data =>
          data.constrs.collectFirst:
            case (constr, sels) if sels.contains(sel) => (constr, sels.indexOf(sel))
      case _ =>
        None

  def all(config: Config, state: State, ctx: Context, bound: List[Var], body: Expr): Expr =
    body match
      case And(phis) => and(config, state, ctx, phis.map(bind(config, state, ctx, All.name, bound, _)))
      case _         => bind(config, state, ctx, All.name, bound, body)

  // exists distributes over or, where each disjunct binds the variables that it uses
  def ex(config: Config, state: State, ctx: Context, bound: List[Var], body: Expr): Expr =
    body match
      case Or(phis) => or(config, state, ctx, phis.map(bind(config, state, ctx, Ex.name, bound, _)))
      case _        => bind(config, state, ctx, Ex.name, bound, body)

  // unused bound variables are dropped,
  // the binder vanishes when none remain (sorts are nonempty in SMT-LIB)
  def bind(config: Config, state: State, ctx: Context, quant: Name, bound: List[Var], body: Expr): Expr =
    val bound_ = bound.filter(body.free.contains)
    if bound_.isEmpty
    then body
    else Bind(quant, bound_, body)

  // eta reduction, the lambda of array type that selects the elements of an array is that array, but not one of
  // function type, e.g. the instance (z) => a[z] of a higher-order variable G of a rule, whose applications G(k) the
  // simplifier reduces to a[k] (see app), which would remain an application of the array otherwise;
  // and the lambda that applies a function value to its variables is that function value
  def lam(config: Config, state: State, ctx: Context, bound: List[Var], body: Expr, typ: Type): Expr =
    (bound, body, typ) match
      case (List(x), Select(base, index), Sort(Con.array, _)) if index == x && !base.free.contains(x) =>
        base

      case (_, Apply(f, args), _) if args == bound && (bound disjoint f.free) =>
        f

      case _ =>
        Lam(bound, body, typ)

  // unused bindings are dropped
  def let(config: Config, state: State, ctx: Context, bound: List[Var], args: List[Expr], body: Expr): Expr =
    val pairs = (bound zip args).filter((x, _) => body.free contains x)
    if pairs.isEmpty
    then body
    else Let(pairs.map(_._1), pairs.map(_._2), body)

  def case_(config: Config, state: State, ctx: Context, pat: Expr, body: Expr, cond: Expr): Case =
    Case(pat, body, cond)

  def match_(config: Config, state: State, ctx: Context, arg: Expr, cases: List[Case]): Expr =
    Match(arg, cases)

  def rec(config: Config, state: State, ctx: Context, fun: Fun, cases: List[Case]): Expr =
    Rec(fun, cases)

  def upd(config: Config, state: State, ctx: Context, cond: Expr, rhs: Expr): Upd =
    Upd(cond, rhs)

  // nested choices are flattened, cases with equal results are merged by the disjunction of their guards,
  // and a single case is its result, e.g. case b => y case c => y is y, which is a trace that keeps its value;
  // where no guard holds, this chooses the value that is not specified, which is unused, since the guards of
  // the updates of trace equation systems hold in all iterations by their iteration constraints;
  // without cases, e.g. when all guards are false, the result of type `typ` is not specified; only cases with equal
  // results are merged, the case distinction of an update is kept otherwise (conditional stores are not merged into
  // stores of conditional values, ideas/conditional-stores.md)
  def eps(config: Config, state: State, ctx: Context, typ: Type, updates: List[Upd]): Expr =
    val merged =
      Eps.flatten(updates).foldLeft(List.empty[Upd]): (merged, update) =>
        merged.indexWhere(other => eq_(config, state, ctx.neutral, other.rhs, update.rhs) == True) match
          case -1 =>
            // otherwise the results are equal under a guard: a result that equals the result of the other case under
            // the guard of that case is the value of both, e.g. k of case k != c => k case k == c => c, since the
            // results are simplified under their guards, which writes k as c under k == c; both are brought into the
            // canonical form of the context of that guard (Classes.normalize, k + 1 is 6 under k == 5), since eq_
            // expects its arguments in the canonical form of its context; only guards with an equation determine a
            // value, so only those are tried
            def covers(rhs: Expr, cond: Expr, rhs_ : Expr) =
              And.flattenStrong(cond).exists { case Eq(_, _) => true; case _ => false } && {
                val inner = ctx.neutral.assume(List(cond), Nil)
                eq_(config, state, inner, inner.classes.normalize(rhs), inner.classes.normalize(rhs_)) == True }

            merged.indexWhere(other => covers(other.rhs, update.cond, update.rhs)) match
              case -1 =>
                merged.indexWhere(other => covers(update.rhs, other.cond, other.rhs)) match
                  case -1 =>
                    merged :+ update

                  case i =>
                    val Upd(cond, _) = merged(i)
                    merged.updated(i, Upd(or(config, state, ctx.neutral, List(cond, update.cond)), update.rhs))

              case i =>
                val Upd(cond, rhs) = merged(i)
                merged.updated(i, Upd(or(config, state, ctx.neutral, List(cond, update.cond)), rhs))

          case i =>
            val Upd(cond, rhs) = merged(i)
            merged.updated(i, Upd(or(config, state, ctx.neutral, List(cond, update.cond)), rhs))

    merged match
      case Nil               => Unspecified(typ)
      case List(Upd(_, rhs)) => rhs
      case _                 => Eps(merged)

  // the conditionals in the results are lifted out of them into cases, the form of the updates of branching statements,
  // which the patterns of the lemmas name, e.g. ret < x[i] ? x[i] : ret of C is case ret < v => v case v <= ret => ret
  def trace(config: Config, state: State, ctx: Context, inits: List[Expr], deps: List[Expr], accs: List[Var], bound: List[Var], results: List[Expr]): Expr =
    val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, results.free -- accs)
    Trace(inits, deps_, accs, bound_, results.map(result => choices(config, state, ctx, re(result))))

  // R[ite(c, a, b)] is case c => R[a] case !c => R[b] for the outermost leftmost conditional that is not below a binder
  // (Normalize.ite), and so on in the cases, also in those of a result that is a choice already; likewise
  // R[eps(cᵢ => vᵢ)] is case cᵢ => R[vᵢ] for a choice nested in a term (Normalize.eps), e.g. the read of a map with
  // cases added to an accumulator, eps(k % 2 == 0 => 2, 0 < k % 2 => 0) + s
  def choices(config: Config, state: State, ctx: Context, result: Expr): Expr =
    result match
      case Eps(updates) =>
        eps(config, state, ctx, result.typ, updates.map(upd => Upd(upd.cond, choices(config, state, ctx, upd.rhs))))

      case _ =>
        Normalize.ite(result) match
          case Some(it @ Ite(test, left, right)) =>
            val updates =
              List(
                Upd(test, choices(config, state, ctx, Normalize.replace(result, it, left))),
                Upd(not(config, state, ctx.neutral, test), choices(config, state, ctx, Normalize.replace(result, it, right)))
              )
            eps(config, state, ctx, result.typ, updates)

          case _ =>
            Normalize.eps(result) match
              case Some(choice @ Eps(updates)) =>
                val updates_ =
                  for Upd(cond, rhs) <- updates
                  yield Upd(cond, choices(config, state, ctx, Normalize.replace(result, choice, rhs)))
                eps(config, state, ctx, result.typ, updates_)

              case _ =>
                result

  // the conditionals of the update are lifted into cases, as in traces, so that a map has one form whether its values
  // come from conditionals or from the cases of an update (see Rewrite.update)
  def maps(config: Config, state: State, ctx: Context, deps: List[Expr], bound: List[Var], update: Expr): Expr =
    val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, update.free)
    Maps(deps_, bound_, choices(config, state, ctx, re(update)))

  // invariants distribute over conjunctions, where each part keeps the dependencies that it uses;
  // with a constant body: true holds trivially,
  // false holds exactly if there are no values, i.e., the dependencies, which have the same length, are nil
  def invs(config: Config, state: State, ctx: Context, deps: List[Expr], bound: List[Var], body: Expr): Expr =
    (deps, body) match
      case (_, And(phis))    => and(config, state, ctx, phis.map(invs(config, state, ctx, deps, bound, _)))
      case (_, True)         => True
      case (dep :: _, False) => Eq(dep, Lists.nil(Type.elem(dep.typ)))
      case _                 =>
        val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, body.free)
        Invs(deps_, bound_, re(body))

  // the dependencies of a combinator, whose bound variables are `bound`, and of whose body `used` are the free variables:
  // equal dependencies are collapsed, whose bound variables are renamed to the first one by the substitution,
  // and those whose bound variables are not used are dropped, except counters, which keep the dependencies nonempty,
  // also variables that denote one by an assumption, e.g. K == counter(0, 1, n) of TEQ.loop (see Context.↑)
  // (if there is none, the first dependency is kept)
  def deps(
      config: Config,
      state: State,
      ctx: Context,
      deps: List[Expr],
      bound: List[Var],
      used: Set[Var]
  ): (List[Expr], List[Var], Subst[Nothing, Var]) =
    val (distinct, re) =
      (deps zip bound).foldLeft[(List[(Expr, Var)], Subst[Nothing, Var])]((Nil, Subst.empty)):
        case ((done, re), (dep, x)) =>
          done.find((dep_, x_) => x_.typ == x.typ && eq_(config, state, ctx.neutral, dep_, dep) == True) match
            case Some((_, x_)) => (done, re + (x -> x_))
            case None          => (done :+ (dep, x), re)

    val used_ = used.map(x => re.vars.getOrElse(x, x))
    val kept =
      distinct.filter:
        case (Butlast(ctx.↑(Counter(_, _, _))), _) => true
        case (_, x)                                => used_ contains x

    val pairs = if kept.isEmpty then distinct.take(1) else kept
    (pairs.map(_._1), pairs.map(_._2), re)
