package cuvee.prove

import cuvee.Debug
import cuvee.Config
import cuvee.Error
import cuvee.core._
import util.intersects

// a simple rewrite engine with the rules of the context (Context.rules), a single step at the top of an expression:
// the first rule whose left hand side matches and whose instantiated condition holds is applied,
// the simplifier traverses the subexpressions and iterates, up to the maximal number of steps of the context
// (Context.withRules), which all rewrites with the context share;
// matching is syntactic modulo
//   the instantiation of the type parameters of the rules,
//   associativity and commutativity of + and - on Int and Real, and their neutral element 0,
//   comparisons as differences, and the symmetry of equations,
//   the binding structure of the combinators trace, map, and all, and the cases of their updates,
//   higher-order patterns, which match by abstraction;
// variables that occur only in the condition of a rule or in the guard of a case are instantiated by matching
// the conjuncts against the facts of the context or the conjuncts of the guard of the expression (see conditions);
// a match is a substitution of the type parameters and variables of the rule
// copied from cuvee.simplify.Rewrite (Oct 13, 2026) and adapted (see doc/prove.md): an expression that a pattern
// does not match is matched by the other members of its class (see Context.defs) and, for the markers of state
// traces, by its view (see Views); a closed side condition is looked up among the facts modulo the classes before it
// is decided
object Rewrite:
  // `self` is the variable that `expr` defines, if it is the right-hand side of an equation (see matches)
  def rewrite(config: Config, state: State, ctx: Context, expr: Expr, self: Option[Var] = None): Expr =
    // note, do not recurse here, the main traversal is in simplify
    expr match
      case _: Var => expr
      case _      => apply(config, state, ctx, ctx.rules, expr, self)

  // a single application of the first rule of the context that applies at the top of `expr`,
  // `expr` itself if none applies (an application always changes the expression)
  def apply(config: Config, state: State, ctx: Context, rules: List[Rule], expr: Expr, self: Option[Var]): Expr =
    rules match
      case Nil =>
        expr

      case rule :: rest =>
        // pick the first rule that matches
        val expr_ = apply(config, state, ctx, rule, expr, self)
        if expr_ != expr
        then expr_
        else apply(config, state, ctx, rest, expr, self)

  // the result of the first match whose instantiated condition holds, `expr` itself if there is none;
  // matching modulo associativity and commutativity may find several matches with different results,
  // e.g. x - y matches a - b with y = b, y = -a, and y = b - a, the first one is taken (see TODO.md)
  def apply(config: Config, state: State, ctx: Context, rule: Rule, expr: Expr, self: Option[Var] = None): Expr =
    if ctx.suspended(rule)
    then expr
    else applyActive(config, state, ctx, rule, expr, self)

  // the rule is suspended while its left-hand side is matched and its conditions are evaluated (see Context.active):
  // a condition that mentions the rule's own term, l == current(Lv) for a rule on current(Lv), would otherwise be
  // rewritten by the rule itself, and a condition that is matched against an invs fact builds the context of that
  // fact's combinator, whose reads the rule would otherwise rewrite into instances of its own left-hand side again
  def applyActive(config: Config, state: State, ctx: Context, rule: Rule, expr: Expr, self: Option[Var]): Expr =
    // the rules applied while matching count only if this rule applies (see Context.applied)
    val applied = ctx.applied.value
    val ctx_ = ctx.copy(active = rule :: ctx.active)
    val results =
      for
        subst <- matches(config, state, ctx_, rule.params, rule.vars, Set(), rule.lhs, self, Map(), Set(), expr, Subst.empty)
        subst_ <- conditions(
          config,
          state,
          ctx_,
          rule.params,
          rule.vars,
          Set(),
          And.flatten(rule.cond),
          None,
          Map(),
          Set(),
          ctx_.known,
          holds(config, state, ctx_, _),
          subst
        )
        // variables of the rule that the match leaves open: those of the left-hand side occur only in cases of the
        // pattern that cover no case of the expression, which never apply, since the cases of the expression hold in
        // all iterations by the iteration constraints, hence any value is an instance, which is not specified,
        // e.g. c of the case D(k, h) => c of current_trace_flag for an update whose cases all keep the value, as the
        // case where D holds left the loop; others, e.g. of the right-hand side only, are an error of the rule
        unbound = rule.rhs.free.intersect(rule.vars) -- subst_.vars.keySet
        _ = Error.report("variables of a rule not instantiated by its match", rule, unbound -- rule.lhs.free, expr):
          require(unbound.subsetOf(rule.lhs.free))
        subst__ = unbound.foldLeft(subst_)((subst, x) => subst + (x -> Unspecified(subst(x.typ))))
        rhs = subst__(rule.rhs)
        // steps that do not change the expression are not applications, e.g. x + 0 = x for x without +
        if rhs != expr
      yield rhs

    results match
      case Nil =>
        // -debug match reports the rules on traces whose left-hand side does not match a trace, e.g. a summary lemma
        // on a view of a trace of several accumulators (see ideas/deduction-engine-plan.md, package M)
        (rule.lhs, expr) match
          case (_: Trace, _: Trace) =>
            Debug.info("match", "no match of " + rule.name.getOrElse("?") + " on " + Simplify.show(config.output.printer, expr))
          case _ =>
        ctx.applied := applied
        expr

      case rhs :: rest =>
        Error.report("rewriting does not terminate", rule):
          require(ctx.steps.value > 0)

        // Error.report("rewriting with multiple result"):
        //    require(rest.isEmpty)

        ctx.steps := ctx.steps.value - 1
        for name <- rule.name
        do ctx.applied := ctx.applied.value.updated(name, ctx.applied.value.getOrElse(name, 0) + 1)
        Debug.step("rewrite", Simplify.show(config.output.printer, expr), Simplify.show(config.output.printer, rhs))
        rhs

  // side conditions and the guards of updates are decided by the simplifier in the context,
  // whose applications of rules count only if the condition holds (see Context.applied)
  def holds(config: Config, state: State, ctx: Context, phi: Expr): Boolean =
    val applied = ctx.applied.value
    val result = phi == True || Simplify.simplify(config, state, ctx.neutral, phi) == True
    if !result then ctx.applied := applied
    result

  def unmatched =
    Nil

  // whether x is instantiated by matching, a variable of the rule or of a dependency
  def mayBind(vars: Set[Var], locals: Set[Var], x: Var) =
    vars.contains(x) || locals.contains(x)

  // a single match if the instance is the argument itself
  def same(inst: Expr, arg: Expr, subst: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    if inst == arg
    then List(subst)
    else unmatched

  // x is instantiated by arg, whose type instantiates that of x
  def bind(state: State, params: Set[Param], x: Var, arg: Expr, subst: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    for subst_ <- matches(state, params, x.typ, arg.typ, subst)
    yield subst_ + (x -> arg)

  // all matches of the pattern `pat` to `arg` that extend `subst`, while matching below the combinators trace, map, and all:
  // `params` are the type parameters of the rule, `vars` are the variables of the rule,
  // `locals` are the bound variables of the pattern that range over dependencies that are variables of the rule,
  // which are instantiated like those, `bound` relates the other bound variables of the pattern to those of the expression,
  // which are among `avoid`, and which the variables of the rule must not capture;
  // `self` is the variable that the expression defines, X in X == trace(...) or Y == maps(...), if it is a combinator
  def matches(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      pat: Expr,
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      arg: Expr,
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    val direct = matches_(config, state, ctx, params, vars, locals, pat, self, bound, avoid, arg, subst)

    // a variable that the pattern does not match as it is, is matched like the other members of its class, its
    // definitions (see Context.defs), e.g. a variable K with K == counter(0, 1, n) by the counter; and a marker of a
    // component of a trace of several accumulators is matched like its simplified view (see Views.projected), which generalizes the
    // definitions of variables to terms
    if direct.nonEmpty || pat.isInstanceOf[Var]
    then direct
    else
      // the definitions are matched with the fallbacks again, since a definition may be a marker whose view matches;
      // this does not recur through the definitions, since only variables have definitions and the members are none
      val defs =
        for
          e <- ctx.defs(arg)
          subst_ <- matches(config, state, ctx, params, vars, locals, pat, self, bound, avoid, e, subst)
        yield
          Debug.step("match", Simplify.show(config.output.printer, arg) + " by its definition", Simplify.show(config.output.printer, e))
          subst_

      if defs.nonEmpty
      then defs
      else
        // a read of a component of a trace of several accumulators is matched structurally first, against the
        // projection of the trace to that component (see Views.structural): a pattern with one accumulator takes
        // the component as its accumulator and the other components as further dependencies, which the selection of
        // dependencies leaves aside like any dependency the pattern does not mention; only if that fails is the
        // normal form of the component computed and matched (see Views.projected), which costs a simplification
        val structural =
          for
            e <- Views.structural(ctx, pat, arg).toList
            subst_ <- matches_(config, state, ctx, params, vars, locals, pat, self, bound, avoid, e, subst)
          yield subst_

        if structural.nonEmpty
        then structural
        else
          Views.projected(config, state, ctx, arg) match
            case Some(e) => matches(config, state, ctx, params, vars, locals, pat, self, bound, avoid, e, subst)
            case None    => unmatched

  def matches_(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      pat: Expr,
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      arg: Expr,
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    (pat, arg) match
      case (x: Var, _) if bound.contains(x) =>
        same(bound(x), arg, subst)

      case (x: Var, _) if mayBind(vars, locals, x) && subst.vars.contains(x) =>
        same(subst.vars(x), arg, subst)

      // the variables of the rule must not capture variables bound in the expression
      case (x: Var, _) if vars.contains(x) && (arg.free intersects avoid) =>
        unmatched

      case (x: Var, _) if mayBind(vars, locals, x) =>
        bind(state, params, x, arg, subst)

      // annotations e as T of the expression are skipped, the left-hand sides of rules have none (see Rules.from)
      case (_, As(inner, _)) =>
        matches(config, state, ctx, params, vars, locals, pat, self, bound, avoid, inner, subst)

      // higher-order patterns F(t₁, ..., tₙ) of a variable of function type, of the rule or of a dependency (locals),
      // applied to distinct bound variables of the pattern (Miller's fragment), or to terms whose variables are instantiated
      // already, e.g. a[k] in a[k := f(a[k])]; they match by abstraction, F = (y₁, ..., yₙ) => expr for the corresponding
      // bound variables of the expression, where all occurrences of the instances of the terms are abstracted, too
      // (see abstraction); the applications in the instantiated right-hand side are beta-reduced by the simplifier
      // (see Simplify.app)
      case (Apply(f: Var, args), _) if mayBind(vars, locals, f) && args.distinct == args =>
        for
          (terms, subst1) <- arguments(state, params, vars, locals, args, bound, avoid, subst)
          if terms.distinct == terms
          subst2 <- abstraction(state, params, vars, f, terms, avoid, arg, subst1)
        yield subst2

      // guarded cases, where a result that is not Eps is a single case whose guard is true,
      // e.g. the update y + 1 of a pattern covers both cases if b then y + 1, if !b then y + 1
      case (Eps(updates), Eps(updates_)) =>
        matches(config, state, ctx, params, vars, locals, updates, self, bound, avoid, updates_, subst)

      case (Eps(updates), _) =>
        matches(config, state, ctx, params, vars, locals, updates, self, bound, avoid, List(Upd(True, arg)), subst)

      case (_, Eps(updates_)) =>
        matches(config, state, ctx, params, vars, locals, List(Upd(True, pat)), self, bound, avoid, updates_, subst)

      // comparisons modulo moving summands between the sides, and < and <= on Int;
      // the constant of the pattern is moved to the expression, whose constants are folded,
      // e.g. k < m is m - k - 1 and matches i < 1024, which is 1023 - i, as m - k against 1024 - i
      case _ if pat.isComparison =>
        for
          (ring, strict, poly) <- comparison(pat)
          (ring_, strict_, poly_) <- comparison(arg)
          if ring == ring_ && strict == strict_
          const = Poly.const(poly.const)
          subst_ <- matches(
            config,
            state,
            ctx,
            params,
            vars,
            locals,
            ring,
            signed(ring, (poly - const).normalize),
            self,
            bound,
            avoid,
            signed(ring, (poly_ - const).normalize),
            true,
            subst
          )
        yield subst_

      case _ if pat.isSum =>
        val Some(ring) = Ring(pat.typ): @unchecked
        // a negation -e is a sum of one summand, which takes no empty sums, otherwise v + w matches -e with w = 0,
        // e.g. sum_add on sum(maps(for xs yield v :: -v)), whose result contains the same sum again
        if arg.typ == ring.typ
        then
          val args = summands(ring, arg)
          matches(config, state, ctx, params, vars, locals, ring, summands(ring, pat), self, bound, avoid, args, arg.isSum && args.length > 1, subst)
        else unmatched

      // equations modulo symmetry, e.g. the pattern a[k] == x matches x == a[i]
      case (App(fun, inst, typ, args), App(fun_, inst_, typ_, args_)) if fun == fun_ && args.length == args_.length =>
        val orders = if fun == Fun.eq_ then List(args_, args_.reverse) else List(args_)
        val substs =
          for
            subst1 <- matches(state, params, inst, inst_, subst)
            subst2 <- matches(state, params, typ, typ_, subst1)
            order <- orders
            subst3 <- matches(config, state, ctx, params, vars, locals, args, self, bound, avoid, order, subst2)
          yield subst3
        substs.distinct

      case (Lit(value, typ), Lit(value_, typ_)) if value == value_ =>
        matches(state, params, typ, typ_, subst)

      // the updates and bodies are matched in the context that the simplifier has there (see Simplify.combinator),
      // which is determined by the expression, e.g. guards follow from the test of the loop
      // a projection of a trace of several accumulators has the history of its component as self (see Views.relation)
      case (Trace.single(init, deps, acc, ys, update), Trace.single(init_, deps_, acc_, ys_, update_)) =>
        val self_ = self.map(x => List((Butlast(x), acc_))).getOrElse(Views.relation(deps_, acc_) match
          case Nil   => ctx.self
          case pairs => pairs)
        lazy val inner = Simplify.combinator(config, state, ctx.bind(List(acc_)).copy(self = self_), deps_, ys_)
        for
          subst1 <- matches(config, state, ctx, params, vars, locals, init, self, bound, avoid, init_, subst)
          subst2 <- combinator(config, state, ctx, params, vars, locals, deps, ys, self, bound, avoid, deps_, ys_, Map(acc -> acc_), subst1):
            (locals_, bound_, avoid_, subst) =>
              matches(config, state, inner, params, vars, locals_, update, None, bound_, avoid_, update_, subst)
        yield subst2

      // a trace of several accumulators, component by component (a lemma over a whole cycle, package O of the plan):
      // the initial values pairwise, the results in the context of the update, where the histories ⌊S⌋.j of the
      // trace that `self` defines denote the accumulators (see Views.selfOf), so that the iteration constraint over
      // them holds there, e.g. lo < hi of the binary search
      case (Trace(inits, deps, accs, ys, results), Trace(inits_, deps_, accs_, ys_, results_))
          if accs.length >= 2 && accs.length == accs_.length =>
        val self_ = self.map(x => Views.selfOf(x, accs_)).getOrElse(ctx.self)
        lazy val inner = Simplify.combinator(config, state, ctx.bind(accs_).copy(self = self_), deps_, ys_)
        for
          subst1 <- matches(config, state, ctx, params, vars, locals, inits, self, bound, avoid, inits_, subst)
          subst2 <- combinator(config, state, ctx, params, vars, locals, deps, ys, self, bound, avoid, deps_, ys_, (accs zip accs_).toMap, subst1):
            (locals_, bound_, avoid_, subst) =>
              matches(config, state, inner, params, vars, locals_, results, None, bound_, avoid_, results_, subst)
        yield subst2

      // the reads of a component of a trace of several accumulators by the same component of a pattern, the trace
      // matched against the definition of the variable it reads, which that variable then defines (self), and
      // otherwise against the variable, i.e. its other definitions, e.g. a name of the trace, bisection(...)
      case (Component(tr, i), Component(s, i_)) if i == i_ =>
        component(config, state, ctx, params, vars, locals, tr, self, bound, avoid, s, subst)

      case (History(tr, i), History(s, i_)) if i == i_ =>
        component(config, state, ctx, params, vars, locals, tr, self, bound, avoid, s, subst)

      // lambdas of the same arity, their bodies with the bound variables related, e.g. the guard m => a[m] < x of a
      // bisection against the pattern m => ar[m] < y of the lemma that names its cut
      case (Lam(xs, body, _), Lam(xs_, body_, _)) if xs.length == xs_.length && xs.types == xs_.types =>
        matches(config, state, ctx, params, vars, locals, body, self, bound ++ (xs zip xs_), avoid ++ xs_, body_, subst)

      case (Maps(deps, ys, update), Maps(deps_, ys_, update_)) =>
        val self_ = self.map(y => (y, update_)).toList
        lazy val inner = Simplify.combinator(config, state, ctx.copy(self = self_), deps_, ys_)
        combinator(config, state, ctx, params, vars, locals, deps, ys, self, bound, avoid, deps_, ys_, Map(), subst):
          (locals_, bound_, avoid_, subst) =>
            matches(config, state, inner, params, vars, locals_, update, None, bound_, avoid_, update_, subst)

      case (Invs(deps, ys, body), Invs(deps_, ys_, body_)) =>
        lazy val inner = Simplify.combinator(config, state, ctx, deps_, ys_)
        combinator(config, state, ctx, params, vars, locals, deps, ys, self, bound, avoid, deps_, ys_, Map(), subst):
          (locals_, bound_, avoid_, subst) =>
            matches(config, state, inner, params, vars, locals_, body, None, bound_, avoid_, body_, subst)

      case _ if pat == arg =>
        List(subst)

      case _ =>
        unmatched

  def matches(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      pats: List[Expr],
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      args: List[Expr],
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    (pats, args) match
      case (Nil, Nil) =>
        List(subst)

      case (pat :: pats_, arg :: args_) =>
        for
          subst1 <- matches(config, state, ctx, params, vars, locals, pat, self, bound, avoid, arg, subst)
          subst2 <- matches(config, state, ctx, params, vars, locals, pats_, self, bound, avoid, args_, subst1)
        yield subst2

      case _ =>
        unmatched

  // sums modulo associativity, commutativity, and the neutral element 0:
  // the summands that are not variables of the pattern are matched to some summand of the same sign first,
  // and the remaining summands are distributed over the variables of the pattern,
  // where all but the last variable take a single summand or none, and the last one takes the rest;
  // variables take the empty sum 0 only if the expression is a sum itself,
  // otherwise e.g. x + 1 would match 1 with x = 0, which rewrites literals inside of sums first,
  // and only if there are fewer summands than variables left, otherwise e.g. v + w would match k + 1
  // also with v = 0 and w = k + 1
  @scala.annotation.targetName("matchesSums")
  def matches(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      ring: Ring,
      pats: List[(Boolean, Expr)],
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      args: List[(Boolean, Expr)],
      sum: Boolean,
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    def flexible(summand: (Boolean, Expr)) =
      summand match
        case (_, x: Var) => mayBind(vars, locals, x) && !subst.vars.contains(x)
        case _           => false

    // a higher-order pattern F(...) whose function is not instantiated yet, which may take several summands like a
    // variable, e.g. M(lo, hi) of M(lo, hi) + 1 against lo + (hi - lo) / 2 + 1 (a probe of a bisection); tried only
    // if the summands do not match otherwise (see below)
    def higher(summand: (Boolean, Expr)) =
      summand match
        case (_, Apply(f: Var, _)) => mayBind(vars, locals, f) && !subst.vars.contains(f)
        case _                     => false

    val (flex, fixed) = pats.partition(flexible)

    def fix(
        fixed: List[(Boolean, Expr)],
        args: List[(Boolean, Expr)],
        subst: Subst[Type, Expr]
    ): List[(List[(Boolean, Expr)], Subst[Type, Expr])] =
      fixed match
        case Nil =>
          List((args, subst))

        case (sign, pat) :: rest =>
          for
            ((sign_, arg), i) <- args.zipWithIndex
            if sign == sign_
            subst_ <- matches(config, state, ctx, params, vars, locals, pat, self, bound, avoid, arg, subst)
            result <- fix(rest, args.patch(i, unmatched, 1), subst_)
          yield result

    def distribute(flex: List[(Boolean, Expr)], args: List[(Boolean, Expr)], subst: Subst[Type, Expr]): List[Subst[Type, Expr]] =
      flex match
        case Nil =>
          if args.isEmpty then List(subst) else unmatched

        // a negated variable -x takes negative summands only, otherwise -x would match every sum,
        // e.g. y + 1 with x = -y - 1, whose result matches again with x = y + 1
        case List((sign, x)) if (args.nonEmpty || sum) && (sign || args.forall(!_._1)) =>
          val rest = if sign then args else negate(args)
          matches(config, state, ctx, params, vars, locals, x, self, bound, avoid, Rewrite.sum(ring, rest), subst)

        case List(_) =>
          unmatched

        case (sign, x) :: flex_ =>
          val single =
            for
              ((sign_, arg), i) <- args.zipWithIndex
              value = if sign == sign_ then arg else ring.uminus(arg)
              subst_ <- matches(config, state, ctx, params, vars, locals, x, self, bound, avoid, value, subst)
              result <- distribute(flex_, args.patch(i, Nil, 1), subst_)
            yield result

          val none =
            for
              subst_ <-
                if sum && args.length < flex.length
                then matches(config, state, ctx, params, vars, locals, x, self, bound, avoid, ring.zero, subst)
                else Nil
              result <- distribute(flex_, args, subst_)
            yield result

          single ++ none

    val results =
      for
        (rest, subst_) <- fix(fixed, args, subst)
        result <- distribute(flex, rest, subst_)
      yield result

    if results.nonEmpty || !fixed.exists(higher)
    then results
    else
      val (flex_, fixed_) = pats.partition(summand => flexible(summand) || higher(summand))
      for
        (rest, subst_) <- fix(fixed_, args, subst)
        result <- distribute(flex_, rest, subst_)
      yield result

  // the dependencies of a combinator in the pattern are partitioned into variables of the rule and other expressions,
  // the latter are matched to a selection of the dependencies of the expression, which relates their bound variables,
  // then the body is matched, which instantiates the bound variables of the pattern for the variables of the rule,
  // from which these are instantiated as the corresponding dependency or as a map over the dependencies of the expression;
  // `acc` relates the accumulator of the pattern to that of the expression
  def combinator(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      deps: List[Expr],
      ys: List[Var],
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      deps_ : List[Expr],
      ys_ : List[Var],
      acc: Map[Var, Var],
      subst: Subst[Type, Expr]
  )(body: (Set[Var], Map[Var, Var], Set[Var], Subst[Type, Expr]) => List[Subst[Type, Expr]]): List[Subst[Type, Expr]] =
    val pairs = deps zip ys
    val (zs, es) =
      pairs.partition:
        case (x: Var, _) => vars.contains(x)
        case _           => false

    val pairs_ = (deps_ zip ys_).zipWithIndex

    // an injective selection of the dependencies of the expression for those of the pattern that are not variables
    def select(es: List[(Expr, Var)], available: List[((Expr, Var), Int)], subst: Subst[Type, Expr]): List[(Map[Var, Var], Subst[Type, Expr])] =
      es match
        case Nil =>
          List((Map(), subst))

        case (dep, y) :: rest =>
          for
            (((dep_, y_), i), k) <- available.zipWithIndex
            subst1 <- matches(config, state, ctx, params, vars, locals, dep, self, bound, avoid, dep_, subst)
            (selected, subst2) <- select(rest, available.patch(k, Nil, 1), subst1)
          yield (selected + (y -> y_), subst2)

    for
      (selected, subst1) <- select(es, pairs_, subst)
      subst2 <- body(locals ++ zs.map(_._2), bound ++ acc ++ selected, avoid ++ ys_ ++ acc.values, subst1)
      subst3 <- instantiate(config, state, ctx, params, vars, locals, zs, self, bound, avoid, deps_, ys_, acc.values.toSet, subst2)
    yield Subst(subst3.params, subst3.vars -- zs.map(_._2))

  // the pattern `tr` of a read of a component against the trace `s` that the read reads (see matches_)
  def component(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      tr: Expr,
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      s: Expr,
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    val defined =
      Views.traceOf(ctx, s) match
        case Some((x: Var, tr_)) => matches(config, state, ctx, params, vars, locals, tr, Some(x), bound, avoid, tr_, subst)
        case _                   => Nil
    if defined.nonEmpty
    then defined
    else matches(config, state, ctx, params, vars, locals, tr, self, bound, avoid, s, subst)

  // the applications of lambdas in `expr` reduced, e.g. the argument M(lo, hi) of a pattern G(M(lo, hi)) once M is
  // instantiated by (l, h) => (h + l) / 2, which is then found as (hi + lo) / 2 in the expression (see abstraction)
  def beta(expr: Expr): Expr =
    expr match
      case Apply(Lam(xs, body, _), args) if xs.length == args.length => beta(Subst.from(xs, args)(body))
      case _                                                         => expr.map(beta)

  // the instances of the arguments of a higher-order pattern: the bound variables of the expression
  // that correspond to the bound variables of the pattern, where those of the variables of the rule
  // among the dependencies (locals) that are not instantiated yet are chosen among the bound variables
  // of the expression, from which the dependency follows (see instantiate); other arguments must be instantiated already
  def arguments(
      state: State,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      args: List[Expr],
      bound: Map[Var, Var],
      avoid: Set[Var],
      subst: Subst[Type, Expr]
  ): List[(List[Expr], Subst[Type, Expr])] =
    args match
      case Nil =>
        List((Nil, subst))

      case arg :: rest =>
        val choices =
          arg match
            case x: Var if bound.contains(x) =>
              List((bound(x), subst))

            case x: Var if locals.contains(x) && !subst.vars.contains(x) =>
              for
                y <- avoid.toList
                subst_ <- bind(state, params, x, y, subst)
              yield (y, subst_)

            case _ if arg.free.forall(x => bound.contains(x) || subst.vars.contains(x) || !mayBind(vars, locals, x)) =>
              List((beta((subst ++ Subst(Map(), bound))(arg)), subst))

            case _ =>
              unmatched

        for
          (term, subst1) <- choices
          (terms, subst2) <- arguments(state, params, vars, locals, rest, bound, avoid, subst1)
        yield (term :: terms, subst2)

  // F = (z₁, ..., zₙ) => arg', where arg' abstracts the instances `terms` of the arguments in `arg`:
  // bound variables of the expression are bound by the lambda, other terms are replaced by fresh variables
  // and must occur in `arg`, otherwise e.g. a[k := f(a[k])] would also match its own result a[k := f(a0[k])];
  // a variable of the rule must not capture other bound variables of the expression, for one of a dependency,
  // the accumulator is excluded by instantiate
  def abstraction(
      state: State,
      params: Set[Param],
      vars: Set[Var],
      f: Var,
      terms: List[Expr],
      avoid: Set[Var],
      arg: Expr,
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    val zs =
      for term <- terms
      yield term match
        case y: Var if avoid.contains(y) => y
        case _                           => Var("z", term.typ).fresh

    val replaced = (terms zip zs).filter((term, z) => term != z)

    def replace(expr: Expr): Expr =
      replaced.collectFirst { case (term, z) if term == expr => z }.getOrElse(expr.map(replace))

    val body = replace(arg)

    subst.vars.get(f) match
      case Some(Lam(xs, body_, _)) =>
        same(Subst.from(xs, terms)(body_), arg, subst)

      case Some(inst) =>
        same(Apply(inst, terms), arg, subst)

      case None if replaced.forall((_, z) => body.free.contains(z))
          && (!vars.contains(f) || (body.free intersect avoid).subsetOf(zs.toSet)) =>
        bind(state, params, f, Lam(zs, body, Arrow(zs.types, body.typ)), subst)

      case None =>
        unmatched

  // the variables of the rule among the dependencies, from the values of their bound variables,
  // which must not depend on the accumulator; a bound variable that the pattern does not use, e.g. in for xs do z, v :: y,
  // takes the front, since any dependency of the expression has the length of the iterations, which are all equal
  def instantiate(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      zs: List[(Expr, Var)],
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      deps_ : List[Expr],
      ys_ : List[Var],
      accs: Set[Var],
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    // the first counter of the iterations, and if there is none, the first dependency of the expression
    val pairs = deps_ zip ys_
    val front = pairs.find((dep_, _) => iterations(ctx, dep_)).getOrElse(pairs.head)

    zs match
      case Nil =>
        List(subst)

      case (z: Var, y) :: rest =>
        val seqs =
          subst.vars.get(y) match
            case Some(value) if value.free intersects accs =>
              Nil

            case Some(value) =>
              ys_.indexOf(value) match
                case k if k >= 0 =>
                  List(deps_(k))

                // the front comes first, also if the value does not use it, followed by the used ones
                case _ =>
                  val used = pairs.filter((_, y_) => value.free.contains(y_))
                  val (deps__, ys__) = (front :: used.filter(_ != front)).unzip
                  List(Maps(deps__, ys__, value))

            case None =>
              List(front._1)

        for
          seq <- seqs
          subst1 <- matches(config, state, ctx, params, vars, locals, z, self, bound, avoid, seq, subst)
          subst2 <- instantiate(config, state, ctx, params, vars, locals, rest, self, bound, avoid, deps_, ys_, accs, subst1)
        yield subst2

      case _ =>
        unmatched

  // each case of the update of the expression is covered by some case of the pattern, whose result matches
  // and whose guard matches or follows from its own (see guard)
  @scala.annotation.targetName("matchesUpdates")
  def matches(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      updates: List[Upd],
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      updates_ : List[Upd],
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    updates_ match
      case Nil =>
        List(subst)

      case Upd(cond_, rhs_) :: rest =>
        val covered =
          for
            Upd(cond, rhs) <- updates
            subst1 <- matches(config, state, ctx, params, vars, locals, rhs, self, bound, avoid, rhs_, subst)
            subst2 <- guard(config, state, ctx, params, vars, locals, cond, self, bound, avoid, cond_, subst1)
          yield subst2
        if covered.isEmpty then
          Debug.info("match", "  no case of the pattern covers " + Simplify.show(config.output.printer, cond_) + " => " + Simplify.show(config.output.printer, rhs_))
        for
          subst2 <- covered
          subst3 <- matches(config, state, ctx, params, vars, locals, updates, self, bound, avoid, rest, subst2)
        yield subst3

  // whether a dependency is the counter of the iterations of a loop, counter(0, 1, n),
  // also one defined by an assumption (see Context.↑)
  def iterations(ctx: Context, dep: Expr): Boolean =
    dep match
      case Butlast(ctx.↑(Counter(Ints.zero, Ints.one, _))) => true
      case _                                             => false

  // the guard of the pattern matches that of the expression, which instantiates the bound variables of the pattern
  // that do not occur in its result, e.g. b in if b then y + 1, and otherwise its conjuncts follow from that of the expression
  // or match its conjuncts (see conditions);
  // a guard D(x, h) && φ of the pattern, whose first conjunct is a higher-order pattern, binds D to the whole guard
  // of the expression, from which the conjuncts of φ must follow in the same way,
  // e.g. the increase x < F(x, h) of a case D(x, h) && x < F(x, h) => F(x, h)
  def guard(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      guard: Expr,
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      guard_ : Expr,
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    def decide(phi: Expr) =
      phi == True || holds(config, state, ctx, Imp(guard_, phi))

    matches(config, state, ctx, params, vars, locals, guard, self, bound, avoid, guard_, subst) match
      case Nil =>
        val whole =
          guard match
            case And((first @ Apply(f: Var, _)) :: rest) if mayBind(vars, locals, f) =>
              for
                subst1 <- matches(config, state, ctx, params, vars, locals, first, self, bound, avoid, guard_, subst)
                subst2 <- conditions(config, state, ctx, params, vars, locals, rest, self, bound, avoid, And.flatten(guard_), decide, subst1)
              yield subst2

            case _ =>
              unmatched

        if whole.nonEmpty then whole
        else
          val parts = conditions(config, state, ctx, params, vars, locals, And.flatten(guard), self, bound, avoid, And.flatten(guard_), decide, subst)
          if parts.isEmpty then
            Debug.info("match", "  guard " + Simplify.show(config.output.printer, guard) + " does not match " + Simplify.show(config.output.printer, guard_))
          parts

      case substs =>
        substs

  // the conjuncts `phis` of a condition of the pattern, the side condition of a rule or a guard, in their order,
  // under `subst`: the variables instantiated so far are substituted and the result simplified, such that
  // e.g. F(x, h) <= b with F = (lo, hi) => (hi + lo) / 2 + 1 is (hi + lo) / 2 + 1 <= b, whose summands are matched
  // as such; a closed instance is decided, an open one is matched against one of the `facts`, also comparisons and
  // equations, which instantiates its variables, e.g. n of sorted(a, n) against a hypothesis, the bound b of
  // F(x, h) <= b against the conjunct mid < p of the guard of the expression, which is mid + 1 <= p on Int, or a and c
  // of 2 * a + p <= b + 2 * c && c < a against the premises of a goal
  def conditions(
      config: Config,
      state: State,
      ctx: Context,
      params: Set[Param],
      vars: Set[Var],
      locals: Set[Var],
      phis: List[Expr],
      self: Option[Var],
      bound: Map[Var, Var],
      avoid: Set[Var],
      facts: List[Expr],
      decide: Expr => Boolean,
      subst: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    phis match
      case Nil =>
        List(subst)

      case phi :: rest =>
        val instance = Simplify.simplify(config, state, ctx.neutral, (subst ++ Subst(Map(), bound))(phi))
        val open = instance.free.exists(x => mayBind(vars, locals, x) && !subst.vars.contains(x))

        // a closed instance is looked up among the facts modulo the classes first (an atom congruent to a fact, e.g.
        // sorted(a, n) for sorted(a, m) with n == m), then decided
        if !open then
          if known(ctx, facts, instance) || decide(instance)
          then conditions(config, state, ctx, params, vars, locals, rest, self, bound, avoid, facts, decide, subst)
          else
            // -debug conditions reports the closed conditions that fail, the first diagnostics of a match that does not
            // go through (see ideas/deduction-engine-plan.md, package M)
            Debug.info("conditions", "not decided: " + Simplify.show(config.output.printer, instance) + " (from " + Simplify.show(config.output.printer, phi) + ")")
            Debug.info("conditions", "  self " + ctx.self.map((t, v) => Simplify.show(config.output.printer, t) + " ~ " + Simplify.show(config.output.printer, v)).mkString(", ") + ", facts on its variables: " + ctx.known.filter(fact => fact.free.intersect(instance.free).nonEmpty).map(Simplify.show(config.output.printer, _)).mkString(" | "))
            unmatched
        else
          for
            fact <- facts
            subst1 <- matches(config, state, ctx, params, vars, locals, instance, self, bound, avoid, fact, subst)
            subst2 <- conditions(config, state, ctx, params, vars, locals, rest, self, bound, avoid, facts, decide, subst1)
          yield subst2

  // whether a closed formula is one of the facts, modulo the classes of the context (the formula is registered in a
  // copy of the classes, which merges it with a fact that is congruent to it) and modulo the canonical forms of
  // terms with binders (see Canon.equal), e.g. an invs condition whose bound variables are named differently from the
  // iteration constraint it is an instance of
  // the canonical comparison is made only with the facts of the same shape (the same constructor, for combinators
  // the same number of dependencies), since the normalization of a fact under the classes costs a traversal
  def known(ctx: Context, facts: List[Expr], phi: Expr): Boolean =
    facts.contains(phi) || {
      val classes = ctx.classes.add(phi)
      lazy val phi_ = classes.normalize(phi)
      facts.exists(fact => classes.equal(fact, phi) || (Canon.binds(phi) && shaped(fact, phi) && Canon.equal(classes.normalize(fact), phi_)))
    }

  def shaped(a: Expr, b: Expr): Boolean =
    (a, b) match
      case (Invs(deps, _, _), Invs(deps_, _, _))       => deps.length == deps_.length
      case (App(f, _, _, _), App(g, _, _, _))           => f == g
      case (Not(a_), Not(b_))                           => shaped(a_, b_)
      case _                                            => a.getClass == b.getClass

  // comparisons on Int and Real as the difference right - left as a normalized polynomial,
  // which is nonnegative, or positive if strict; on Int, left < right is left + 1 <= right, hence never strict;
  // > and >= do not occur, the simplifier turns them into < and <= before rewriting
  def comparison(expr: Expr): List[(Ring, Boolean, Poly)] =
    def difference(ring: Ring, left: Expr, right: Expr, offset: Int) =
      (Arith.toPoly(ring, right) - Arith.toPoly(ring, left) - Poly.const(util.Rational(offset))).normalize

    expr match
      case Ints.lt(left, right)  => List((Ints.ring, false, difference(Ints.ring, left, right, 1)))
      case Ints.le(left, right)  => List((Ints.ring, false, difference(Ints.ring, left, right, 0)))
      case Reals.lt(left, right) => List((Reals.ring, true, difference(Reals.ring, left, right, 0)))
      case Reals.le(left, right) => List((Reals.ring, false, difference(Reals.ring, left, right, 0)))
      case _                    => Nil

  // the summands of a polynomial with their signs, whose factors and constant are positive
  def signed(ring: Ring, poly: Poly): List[(Boolean, Expr)] =
    val monos =
      for mono <- poly.monos
      yield
        if mono.factor.isNegative
        then (false, (-mono).toExpr(ring))
        else (true, mono.toExpr(ring))

    val const =
      if poly.const.isZero then Nil
      else if poly.const.isNegative then List((false, ring.lit(-poly.const)))
      else List((true, ring.lit(poly.const)))

    monos ++ const

  // the summands of a sum with their signs, where 0 is dropped
  def summands(ring: Ring, expr: Expr): List[(Boolean, Expr)] =
    expr match
      case ring.zero               => Nil
      case ring.plus(args)         => for arg <- args; summand <- summands(ring, arg) yield summand
      case ring.minus(left, right) => summands(ring, left) ++ negate(summands(ring, right))
      case ring.uminus(arg)        => negate(summands(ring, arg))
      case _                       => List((true, expr))

  def negate(summands: List[(Boolean, Expr)]): List[(Boolean, Expr)] =
    for (sign, expr) <- summands
    yield (!sign, expr)

  // the sum of the summands, the positive ones first, which is 0 if there are none
  def sum(ring: Ring, summands: List[(Boolean, Expr)]): Expr =
    val pos = summands.filter(_._1).map(_._2)
    val neg = summands.filterNot(_._1).map(_._2)

    (pos, neg) match
      case (Nil, Nil)     => ring.zero
      case (Nil, n :: ns) => ns.foldLeft(ring.uminus(n))(ring.minus(_, _))
      case (_, _)         => neg.foldLeft(ring.plus(pos))(ring.minus(_, _))

  // the type parameters `params` of the rule in the pattern are instantiated consistently, a single match or none,
  // other type parameters are constants; defined sorts are expanded in both already (see Type.expand)
  def matches(state: State, params: Set[Param], pat: Type, typ: Type, subst: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    (pat, typ) match
      case (p: Param, _) if params.contains(p) =>
        subst.params.get(p) match
          case Some(t) => if t == typ then List(subst) else unmatched
          case None    => List(subst + (p -> typ))

      case (Sort(con, args), Sort(con_, args_)) if con == con_ =>
        matches(state, params, args, args_, subst)

      case _ if pat == typ =>
        List(subst)

      case _ =>
        unmatched

  @scala.annotation.targetName("matchesTypes")
  def matches(state: State, params: Set[Param], pats: List[Type], types_ : List[Type], subst: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    (pats, types_) match
      case (Nil, Nil) =>
        List(subst)

      case (pat :: pats_, typ :: types__) =>
        for
          subst1 <- matches(state, params, pat, typ, subst)
          subst2 <- matches(state, params, pats_, types__, subst1)
        yield subst2

      case _ =>
        unmatched
