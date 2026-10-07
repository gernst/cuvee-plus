package cuvee.simplify

import cuvee.Debug
import cuvee.Config
import cuvee.Error
import cuvee.core._

// the variables while matching below the combinators trace, map, and all:
// `vars` are the variables of the rule, `locals` are the bound variables of the pattern that range over dependencies
// that are variables of the rule, which are instantiated like those, `local` relates the other bound variables
// of the pattern to those of the expression, which are `bound`, and which the variables of the rule must not capture;
// `self` is the variable that the expression defines, X in X == trace(...) or Y == maps(...), if it is a combinator
case class Binding(vars: Set[Var], locals: Set[Var], local: Map[Var, Var], bound: Set[Var], self: Option[Var] = None):
  def isPattern(x: Var) =
    vars.contains(x) || locals.contains(x)

  // bound variables of the pattern, the arguments of higher-order patterns
  def isBound(expr: Expr) =
    expr match
      case x: Var => local.contains(x) || locals.contains(x)
      case _      => false

// a simple rewrite engine with the rules of the context (Ctx.rules), a single step at the top of an expression:
// the first rule whose left hand side matches and whose instantiated condition holds is applied,
// the simplifier traverses the subexpressions and iterates, up to the maximal number of steps of the context
// (Ctx.withRules), which all rewrites with the context share;
// matching is syntactic modulo
//   the instantiation of the type parameters of the rules,
//   associativity and commutativity of + and - on Int and Real, and their neutral element 0,
//   the binding structure of the combinators trace, map, and all
// a match is a substitution of the type parameters and variables of the rule
object Rewrite:
  // `self` is the variable that `expr` defines, if it is the right-hand side of an equation (see Binding)
  def rewrite(config: Config, state: State, ctx: Ctx, expr: Expr, self: Option[Var] = None): Expr =
    // note, do not recurse here, the main traversal is in simplify
    expr match
      case _: Var => expr
      case _      => apply(config, state, ctx, ctx.rules, expr, self)

  // a single application of the first rule of the context that applies at the top of `expr`,
  // `expr` itself if none applies (an application always changes the expression)
  def apply(config: Config, state: State, ctx: Ctx, rules: List[Rule], expr: Expr, self: Option[Var]): Expr =
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
  def apply(config: Config, state: State, ctx: Ctx, rule: Rule, expr: Expr, self: Option[Var] = None): Expr =
    val results =
      for
        su <- matches(config, state, ctx, Binding(rule.xs.toSet, Set(), Map(), Set(), self), rule.lhs, expr, Subst.empty)
        rhs = su(rule.rhs)
        // steps that do not change the expression are not applications, e.g. x + 0 = x for x without +
        if rhs != expr && holds(config, state, ctx, su(rule.cond))
      yield rhs

    results match
      case Nil =>
        expr

      case rhs :: rest =>
        Error.report("rewriting does not terminate", rule):
          require(ctx.steps.value > 0)

        // if rest.nonempty
        // for expr <- results
        // do println(Simplify.show(config.input.printer, expr))

        // Error.raise("rewriting with multiple result")

        ctx.steps := ctx.steps.value - 1
        Debug.step("rewrite", Simplify.show(config.output.printer, expr), Simplify.show(config.output.printer, rhs))
        rhs


  // side conditions and the guards of updates are decided by the simplifier in the context
  def holds(config: Config, state: State, ctx: Ctx, phi: Expr): Boolean =
    phi == True || Simplify.simplify(config, state, ctx.neutral, phi) == True

  // all matches of the pattern `pat` to `expr` that extend `m`
  def matches(config: Config, state: State, ctx: Ctx, b: Binding, pat: Expr, expr: Expr, m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    (pat, expr) match
      case (x: Var, _) if b.local.contains(x) =>
        if expr == b.local(x) then List(m) else Nil

      case (x: Var, _) if b.isPattern(x) =>
        m.vars.get(x) match
          case Some(e) =>
            if e == expr then List(m) else Nil

          // the variables of the rule must not capture variables bound in the expression
          case None if b.vars.contains(x) && (expr.free intersect b.bound).nonEmpty =>
            Nil

          case None =>
            for m_ <- matches(state, x.typ, expr.typ, m)
            yield m_ + (x -> expr)

      // annotations e as T of the expression are skipped, the left-hand sides of rules have none (see Rules.from)
      case (_, As(arg, _)) =>
        matches(config, state, ctx, b, pat, arg, m)

      // higher-order patterns F(t₁, ..., tₙ) of a variable of function type, of the rule or of a dependency (Binding.locals),
      // applied to distinct bound variables of the pattern (Miller's fragment), or to terms whose variables are instantiated
      // already, e.g. a[k] in a[k := f(a[k])]; they match by abstraction, F = (y₁, ..., yₙ) => expr for the corresponding
      // bound variables of the expression, where all occurrences of the instances of the terms are abstracted, too
      // (see abstraction); the applications in the instantiated right-hand side are beta-reduced by the simplifier
      // (see Simplify.app)
      case (Apply(f: Var, args), _) if b.isPattern(f) && args.distinct == args =>
        for
          (terms, m1) <- arguments(state, b, args, m)
          if terms.distinct == terms
          m2 <- abstraction(state, b, f, terms, expr, m1)
        yield m2

      // guarded cases, where a result that is not Eps is a single case whose guard is true,
      // e.g. the update y + 1 of a pattern covers both cases if b then y + 1, if !b then y + 1
      case (Eps(updates), Eps(updates_)) =>
        matches(config, state, ctx, b, updates, updates_, m)

      case (Eps(updates), _) =>
        matches(config, state, ctx, b, updates, List(Upd(True, expr)), m)

      case (_, Eps(updates_)) =>
        matches(config, state, ctx, b, List(Upd(True, pat)), updates_, m)

      // comparisons modulo moving summands between the sides, and < and <= on Int;
      // the constant of the pattern is moved to the expression, whose constants are folded,
      // e.g. k < m is m - k - 1 and matches i < 1024, which is 1023 - i, as m - k against 1024 - i
      case _ if pat.isComparison =>
        for
          (ring, strict, poly) <- comparison(pat)
          (ring_, strict_, poly_) <- comparison(expr)
          if ring == ring_ && strict == strict_
          const = Poly.const(poly.const)
          m_ <- matches(
            config,
            state,
            ctx,
            b,
            ring,
            signed(ring, (poly - const).normalize),
            signed(ring, (poly_ - const).normalize),
            true,
            m
          )
        yield m_

      case _ if pat.isSum =>
        val Some(ring) = Ring(pat.typ): @unchecked
        if expr.typ == ring.typ
        then matches(config, state, ctx, b, ring, summands(ring, pat), summands(ring, expr), expr.isSum, m)
        else Nil

      // equations modulo symmetry, e.g. the pattern a[k] == x matches x == a[i]
      case (App(Fun.eq_, inst, typ, args), App(Fun.eq_, inst_, typ_, args_)) =>
        val ms =
          for
            m1 <- matches(state, inst, inst_, m)
            m2 <- matches(state, typ, typ_, m1)
            m3 <- matches(config, state, ctx, b, args, args_, m2) ++ matches(config, state, ctx, b, args, args_.reverse, m2)
          yield m3
        ms.distinct

      case (App(fun, inst, typ, args), App(fun_, inst_, typ_, args_)) if fun == fun_ && args.length == args_.length =>
        for
          m1 <- matches(state, inst, inst_, m)
          m2 <- matches(state, typ, typ_, m1)
          m3 <- matches(config, state, ctx, b, args, args_, m2)
        yield m3

      case (Lit(value, typ), Lit(value_, typ_)) if value == value_ =>
        matches(state, typ, typ_, m)

      // the updates and bodies are matched in the context that the simplifier has there (see Simplify.combinator),
      // which is determined by the expression, e.g. guards follow from the test of the loop
      case (Trace(init, deps, acc, bound, update), Trace(init_, deps_, acc_, bound_, update_)) =>
        val self = b.self.map(x => (Butlast(x), acc_))
        val inner = Simplify.combinator(config, state, ctx.bind(List(acc_)), deps_, bound_, self)
        for
          m1 <- matches(config, state, ctx, b, init, init_, m)
          m2 <- combinator(config, state, ctx, b, deps, bound, deps_, bound_, Map(acc -> acc_), m1): (b_, m) =>
            matches(config, state, inner, b_, update, update_, m)
        yield m2

      case (Maps(deps, bound, update), Maps(deps_, bound_, update_)) =>
        val self = b.self.map(y => (y, update_))
        val inner = Simplify.combinator(config, state, ctx, deps_, bound_, self)
        combinator(config, state, ctx, b, deps, bound, deps_, bound_, Map(), m): (b_, m) =>
          matches(config, state, inner, b_, update, update_, m)

      case (Invs(deps, bound, body), Invs(deps_, bound_, body_)) =>
        val inner = Simplify.combinator(config, state, ctx, deps_, bound_)
        combinator(config, state, ctx, b, deps, bound, deps_, bound_, Map(), m): (b_, m) =>
          matches(config, state, inner, b_, body, body_, m)

      case _ if pat == expr =>
        List(m)

      // a variable x of the expression with an equation x == e in the context is matched like e (see Ctx.↑),
      // only if the pattern is not a variable, which binds x itself (see above);
      // equations between variables are not followed, since they may be cyclic
      case (_, x @ ctx.↑(e)) if e != x && !e.isInstanceOf[Var] =>
        matches(config, state, ctx, b, pat, e, m)

      case _ =>
        Nil

  def matches(
      config: Config,
      state: State,
      ctx: Ctx,
      b: Binding,
      pats: List[Expr],
      exprs: List[Expr],
      m: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    (pats, exprs) match
      case (Nil, Nil) =>
        List(m)

      case (pat :: pats_, expr :: exprs_) =>
        matches(config, state, ctx, b, pat, expr, m).flatMap(matches(config, state, ctx, b, pats_, exprs_, _))

      case _ =>
        Nil

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
      ctx: Ctx,
      b: Binding,
      ring: Ring,
      pats: List[(Boolean, Expr)],
      exprs: List[(Boolean, Expr)],
      sum: Boolean,
      m: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    def flexible(summand: (Boolean, Expr)) =
      summand match
        case (_, x: Var) => b.isPattern(x) && !m.vars.contains(x)
        case _           => false

    val (flex, fixed) = pats.partition(flexible)

    def fix(
        fixed: List[(Boolean, Expr)],
        exprs: List[(Boolean, Expr)],
        m: Subst[Type, Expr]
    ): List[(List[(Boolean, Expr)], Subst[Type, Expr])] =
      fixed match
        case Nil =>
          List((exprs, m))

        case (sign, pat) :: rest =>
          for
            ((sign_, expr), i) <- exprs.zipWithIndex
            if sign == sign_
            m_ <- matches(config, state, ctx, b, pat, expr, m)
            result <- fix(rest, exprs.patch(i, Nil, 1), m_)
          yield result

    def distribute(flex: List[(Boolean, Expr)], exprs: List[(Boolean, Expr)], m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
      flex match
        case Nil =>
          if exprs.isEmpty then List(m) else Nil

        // a negated variable -x takes negative summands only, otherwise -x would match every sum,
        // e.g. y + 1 with x = -y - 1, whose result matches again with x = y + 1
        case List((sign, x)) if (exprs.nonEmpty || sum) && (sign || exprs.forall(!_._1)) =>
          val rest = if sign then exprs else negate(exprs)
          matches(config, state, ctx, b, x, Rewrite.sum(ring, rest), m)

        case List(_) =>
          Nil

        case (sign, x) :: flex_ =>
          val single =
            for
              ((sign_, expr), i) <- exprs.zipWithIndex
              value = if sign == sign_ then expr else ring.uminus(expr)
              m_ <- matches(config, state, ctx, b, x, value, m)
              result <- distribute(flex_, exprs.patch(i, Nil, 1), m_)
            yield result

          val none =
            for
              m_ <- if sum && exprs.length < flex.length then matches(config, state, ctx, b, x, ring.lit(util.Rational(0)), m) else Nil
              result <- distribute(flex_, exprs, m_)
            yield result

          single ++ none

    for
      (rest, m_) <- fix(fixed, exprs, m)
      result <- distribute(flex, rest, m_)
    yield result

  // the dependencies of a combinator in the pattern are partitioned into variables of the rule and other expressions,
  // the latter are matched to a selection of the dependencies of the expression, which relates their bound variables,
  // then the body is matched, which instantiates the bound variables of the pattern for the variables of the rule,
  // from which these are instantiated as the corresponding dependency or as a map over the dependencies of the expression
  def combinator(
      config: Config,
      state: State,
      ctx: Ctx,
      b: Binding,
      deps: List[Expr],
      bound: List[Var],
      deps_ : List[Expr],
      bound_ : List[Var],
      local: Map[Var, Var],
      m: Subst[Type, Expr]
  )(body: (Binding, Subst[Type, Expr]) => List[Subst[Type, Expr]]): List[Subst[Type, Expr]] =
    val pairs = deps zip bound
    val (zs, es) =
      pairs.partition:
        case (x: Var, _) => b.vars.contains(x)
        case _           => false

    val pairs_ = (deps_ zip bound_).zipWithIndex

    // an injective selection of the dependencies of the expression for those of the pattern that are not variables
    def select(es: List[(Expr, Var)], available: List[((Expr, Var), Int)], m: Subst[Type, Expr]): List[(Map[Var, Var], Subst[Type, Expr])] =
      es match
        case Nil =>
          List((Map(), m))

        case (dep, y) :: rest =>
          for
            (((dep_, y_), i), k) <- available.zipWithIndex
            m1 <- matches(config, state, ctx, b, dep, dep_, m)
            (local, m2) <- select(rest, available.patch(k, Nil, 1), m1)
          yield (local + (y -> y_), m2)

    for
      (selected, m1) <- select(es, pairs_, m)
      b_ = Binding(b.vars, b.locals ++ zs.map(_._2), b.local ++ local ++ selected, b.bound ++ bound_ ++ local.values)
      m2 <- body(b_, m1)
      m3 <- instantiate(config, state, ctx, b, zs, deps_, bound_, local.values.toSet, m2)
    yield Subst(m3.params, m3.vars -- zs.map(_._2))

  // the instances of the arguments of a higher-order pattern: the bound variables of the expression
  // that correspond to the bound variables of the pattern, where those of the variables of the rule
  // among the dependencies (Binding.locals) that are not instantiated yet are chosen among the bound variables
  // of the expression, from which the dependency follows (see instantiate); other arguments must be instantiated already
  def arguments(state: State, b: Binding, args: List[Expr], m: Subst[Type, Expr]): List[(List[Expr], Subst[Type, Expr])] =
    args match
      case Nil =>
        List((Nil, m))

      case arg :: rest =>
        val choices =
          arg match
            case x: Var if b.local.contains(x) =>
              List((b.local(x), m))

            case x: Var if b.locals.contains(x) && !m.vars.contains(x) =>
              for
                y <- b.bound.toList
                m_ <- matches(state, x.typ, y.typ, m)
              yield (y, m_ + (x -> y))

            case _ if arg.free.forall(x => b.local.contains(x) || m.vars.contains(x) || !b.isPattern(x)) =>
              List(((m ++ Subst(Map(), b.local))(arg), m))

            case _ =>
              Nil

        for
          (term, m1) <- choices
          (terms, m2) <- arguments(state, b, rest, m1)
        yield (term :: terms, m2)

  // F = (z₁, ..., zₙ) => expr', where expr' abstracts the instances `terms` of the arguments in `expr`:
  // bound variables of the expression are bound by the lambda, other terms are replaced by fresh variables
  // and must occur in `expr`, otherwise e.g. a[k := f(a[k])] would also match its own result a[k := f(a0[k])];
  // a variable of the rule must not capture other bound variables of the expression, for one of a dependency,
  // the accumulator is excluded by instantiate
  def abstraction(state: State, b: Binding, f: Var, terms: List[Expr], expr: Expr, m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    val zs =
      for term <- terms
      yield term match
        case y: Var if b.bound.contains(y) => y
        case _                             => Var("z", term.typ).fresh

    val replaced = (terms zip zs).filter((term, z) => term != z)

    def replace(expr: Expr): Expr =
      replaced.collectFirst { case (term, z) if term == expr => z }.getOrElse(expr.map(replace))

    val body = replace(expr)

    m.vars.get(f) match
      case Some(Lam(xs, body_, _)) =>
        if Subst.from(xs, terms)(body_) == expr then List(m) else Nil

      case Some(value) =>
        if Apply(value, terms) == expr then List(m) else Nil

      case None if replaced.forall((_, z) => body.free.contains(z))
          && (!b.vars.contains(f) || (body.free intersect b.bound).subsetOf(zs.toSet)) =>
        val lam = Lam(zs, body, Arrow(zs.types, body.typ))
        for m_ <- matches(state, f.typ, lam.typ, m)
        yield m_ + (f -> lam)

      case None =>
        Nil

  // the variables of the rule among the dependencies, from the values of their bound variables,
  // which must not depend on the accumulator
  def instantiate(
      config: Config,
      state: State,
      ctx: Ctx,
      b: Binding,
      zs: List[(Expr, Var)],
      deps_ : List[Expr],
      bound_ : List[Var],
      accs: Set[Var],
      m: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    // the first counter of the iterations, and if there is none, the first dependency of the expression
    val pairs = deps_ zip bound_
    val front = pairs.find((dep_, _) => iterations(ctx, dep_)).getOrElse(pairs.head)

    zs match
      case Nil =>
        List(m)

      case (z: Var, y) :: rest if m.vars.contains(y) =>
        val value = m.vars(y)
        val seq =
          bound_.indexOf(value) match
            case k if k >= 0 =>
              deps_(k)

            // the front comes first, also if the value does not use it, followed by the used ones
            case _ =>
              val used = pairs.filter((_, y_) => value.free.contains(y_))
              val (deps__, bound__) = (front :: used.filter(_ != front)).unzip
              Maps(deps__, bound__, value)

        if (value.free intersect accs).nonEmpty
        then Nil
        else
          for
            m1 <- matches(config, state, ctx, b, z, seq, m)
            m2 <- instantiate(config, state, ctx, b, rest, deps_, bound_, accs, m1)
          yield m2

      // the bound variable is unused by the pattern, e.g. in for xs do z, v :: y,
      // then any dependency of the expression has the length of the iterations, which are all equal
      case (z: Var, y) :: rest =>
        for
          m1 <- matches(config, state, ctx, b, z, front._1, m)
          m2 <- instantiate(config, state, ctx, b, rest, deps_, bound_, accs, m1)
        yield m2

      case _ =>
        Nil

  // each case of the update of the expression is covered by some case of the pattern, whose guard follows from its own
  @scala.annotation.targetName("matchesUpdates")
  def matches(
      config: Config,
      state: State,
      ctx: Ctx,
      b: Binding,
      updates: List[Upd],
      updates_ : List[Upd],
      m: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    updates_ match
      case Nil =>
        List(m)

      case Upd(cond_, rhs_) :: rest =>
        for
          Upd(cond, rhs) <- updates
          m1 <- matches(config, state, ctx, b, rhs, rhs_, m)
          m2 <- guard(config, state, ctx, b, cond_, cond, m1)
          m3 <- matches(config, state, ctx, b, updates, rest, m2)
        yield m3

  // whether a dependency is the counter of the iterations of a loop, counter(0, 1, n),
  // also one defined by an assumption (see Ctx.↑)
  def iterations(ctx: Ctx, dep: Expr): Boolean =
    dep match
      case Butlast(ctx.↑(Counter(Zero.int, One.int, _))) => true
      case _                                             => false

  // the guard of the pattern matches that of the expression, which instantiates the bound variables of the pattern
  // that do not occur in its result, e.g. b in if b then y + 1, and otherwise it must follow from that of the expression;
  // a guard D(x, h) && φ of the pattern, whose first conjunct is a higher-order pattern, binds D to the whole guard
  // of the expression, from which the conjuncts of φ must follow (see conjuncts),
  // e.g. the increase x < F(x, h) of a case D(x, h) && x < F(x, h) => F(x, h)
  def guard(config: Config, state: State, ctx: Ctx, b: Binding, guard_ : Expr, guard: Expr, m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    matches(config, state, ctx, b, guard, guard_, m) match
      case Nil =>
        val whole =
          guard match
            case And((first @ Apply(f: Var, _)) :: rest) if b.isPattern(f) =>
              for
                m1 <- matches(config, state, ctx, b, first, guard_, m)
                m2 <- conjuncts(config, state, ctx, b, guard_, rest, m1)
              yield m2

            case _ =>
              Nil

        if whole.nonEmpty then whole
        else if implies(config, state, ctx, b, guard_, guard, m) then List(m)
        else Nil

      case ms =>
        ms

  // the conjuncts `phis` of the guard of a pattern follow from the guard of the expression: each is matched against one
  // of its conjuncts, which may instantiate further variables, e.g. the bound b of F(x, h) <= b against mid < p,
  // which is mid + 1 <= p on Int, and otherwise it must follow from the guard of the expression;
  // the variables instantiated so far are substituted and the result simplified before it is matched,
  // such that e.g. F(x, h) <= b with F = (lo, hi) => (hi + lo) / 2 + 1 is (hi + lo) / 2 + 1 <= b,
  // whose summands are matched as such
  def conjuncts(
      config: Config,
      state: State,
      ctx: Ctx,
      b: Binding,
      guard_ : Expr,
      phis: List[Expr],
      m: Subst[Type, Expr]
  ): List[Subst[Type, Expr]] =
    phis match
      case Nil =>
        List(m)

      case phi :: rest =>
        val su = m ++ Subst.from(b.local.keys.toList, b.local.values.toList)
        val instance = Simplify.simplify(config, state, ctx.neutral, su(phi))
        val matched =
          for
            phi_ <- And.flatten(guard_)
            m_ <- matches(config, state, ctx, b, instance, phi_, m)
          yield m_

        val ms =
          if matched.nonEmpty then matched
          else if implies(config, state, ctx, b, guard_, phi, m) then List(m)
          else Nil

        ms.flatMap(conjuncts(config, state, ctx, b, guard_, rest, _))

  def implies(config: Config, state: State, ctx: Ctx, b: Binding, guard_ : Expr, guard: Expr, m: Subst[Type, Expr]): Boolean =
    if guard == True
    then true
    else
      val su = m ++ Subst.from(b.local.keys.toList, b.local.values.toList)
      val guard__ = su(guard)
      val open = guard__.free.exists(x => b.isPattern(x) && !m.vars.contains(x))
      !open && holds(config, state, ctx, Imp(guard_, guard__))

  // comparisons on Int and Real as the difference right - left as a normalized polynomial,
  // which is nonnegative, or positive if strict; on Int, left < right is left + 1 <= right, hence never strict;
  // > and >= do not occur, the simplifier turns them into < and <= before rewriting
  def comparison(expr: Expr): List[(Ring, Boolean, Poly)] =
    def difference(ring: Ring, left: Expr, right: Expr, offset: Int) =
      (Arith.toPoly(ring, right) - Arith.toPoly(ring, left) - Poly.const(util.Rational(offset))).normalize

    expr match
      case Lt.int(left, right)  => List((Ring.int, false, difference(Ring.int, left, right, 1)))
      case Le.int(left, right)  => List((Ring.int, false, difference(Ring.int, left, right, 0)))
      case Lt.real(left, right) => List((Ring.real, true, difference(Ring.real, left, right, 0)))
      case Le.real(left, right) => List((Ring.real, false, difference(Ring.real, left, right, 0)))
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
      case ring.plus(args)         => args.flatMap(summands(ring, _))
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
      case (Nil, Nil)     => ring.lit(util.Rational(0))
      case (Nil, n :: ns) => ns.foldLeft(ring.uminus(n))(ring.minus(_, _))
      case (_, _)         => neg.foldLeft(ring.plus(pos))(ring.minus(_, _))

  // the type parameters of the pattern are instantiated consistently, a single match or none;
  // defined sorts are expanded in both already (see Type.expand)
  def matches(state: State, pat: Type, typ: Type, m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    (pat, typ) match
      case (p: Param, _) =>
        m.params.get(p) match
          case Some(t) => if t == typ then List(m) else Nil
          case None    => List(m + (p -> typ))

      case (Sort(con, args), Sort(con_, args_)) if con == con_ =>
        matches(state, args, args_, m)

      case _ =>
        Nil

  @scala.annotation.targetName("matchesTypes")
  def matches(state: State, pats: List[Type], types_ : List[Type], m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    if pats.length != types_.length
    then Nil
    else
      (pats zip types_).foldLeft(List(m)):
        case (ms, (pat, typ)) => ms.flatMap(matches(state, pat, typ, _))
