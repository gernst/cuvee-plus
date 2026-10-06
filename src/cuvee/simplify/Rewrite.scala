package cuvee.simplify

import cuvee.Debug
import cuvee.Config
import cuvee.Error
import cuvee.core._

// the variables while matching below the combinators trace, map, and all:
// `vars` are the variables of the rule, `locals` are the bound variables of the pattern that range over dependencies
// that are variables of the rule, which are instantiated like those, `local` relates the other bound variables
// of the pattern to those of the expression, which are `bound`, and which the variables of the rule must not capture
case class Binding(vars: Set[Var], locals: Set[Var], local: Map[Var, Var], bound: Set[Var]):
  def isPattern(x: Var) =
    vars.contains(x) || locals.contains(x)

// a simple rewrite engine with the rules of the context (Ctx.rules): expressions are rewritten innermost first,
// at each position the first rule whose left hand side matches and whose instantiated condition holds is applied,
// and the result is rewritten again, up to the maximal number of steps of the context (Ctx.withRules);
// matching is syntactic modulo
//   the instantiation of the type parameters of the rules,
//   associativity and commutativity of + and - on Int and Real, and their neutral element 0,
//   the binding structure of the combinators trace, map, and all (see Trace Equation Systems, section 5.2);
// a match is a substitution of the type parameters and variables of the rule
object Rewrite:
  // rewrite `expr` with `rules` until no rule applies
  def apply(rules: List[Rule], expr: Expr): Expr =
    rewrite(Config.default, State.empty, Ctx.empty.withRules(rules), expr)

  def rewrite(config: Config, state: State, ctx: Ctx, expr: Expr): Expr =
    val expr_ = expr.map(rewrite(config, state, ctx, _))
    val next = step(config, state, ctx, expr_)
    if next == expr_
    then expr_
    else rewrite(config, state, ctx, next)

  // a single application of the first rule of the context that applies at the top of `expr`,
  // `expr` itself if none applies (an application always changes the expression)
  def step(config: Config, state: State, ctx: Ctx, expr: Expr): Expr =
    ctx.rules.iterator
      .map(rule => apply(config, state, ctx, rule, expr))
      .find(_ != expr)
      .getOrElse(expr)

  // the result of the first match whose instantiated condition holds, `expr` itself if there is none;
  // matching modulo associativity and commutativity may find several matches with different results,
  // e.g. x - y matches a - b with y = b, y = -a, and y = b - a, the first one is taken (see TODO.md)
  def apply(config: Config, state: State, ctx: Ctx, rule: Rule, expr: Expr): Expr =
    // variables are not rewritten by following their equations, only inside of expressions
    if expr.isInstanceOf[Var] then return expr
    val results =
      for
        su <- matches(config, state, ctx, Binding(rule.xs.toSet, Set(), Map(), Set()), rule.lhs, expr, Subst.empty)
        rhs = su(rule.rhs)
        // steps that do not change the expression are not applications, e.g. x + 0 = x for x without +
        if rhs != expr && holds(config, state, ctx, su(rule.cond))
      yield rhs

    results.headOption match
      case None => expr
      case Some(rhs) =>
        Error.report("rewriting does not terminate", rule, expr):
          require(ctx.steps.value > 0)
        ctx.steps := ctx.steps.value - 1
        Debug.step("rewrite", Simplify.show(config.printer, expr), Simplify.show(config.printer, rhs))
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
            for m_ <- Rewrite.matches(x.typ, expr.typ, m)
            yield m_ + (x -> expr)

      // comparisons modulo moving summands between the sides, and < and <= on Int
      case _ if Rewrite.comparison(pat).nonEmpty =>
        for
          (ring, strict, poly) <- Rewrite.comparison(pat)
          (ring_, strict_, poly_) <- Rewrite.comparison(expr)
          if ring == ring_ && strict == strict_
          m_ <- matches(config, state, ctx, b, ring, Rewrite.signed(ring, poly), Rewrite.signed(ring, poly_), true, m)
        yield m_

      case _ if Rewrite.arithmetic(pat) =>
        val Some(ring) = Ring(pat.typ): @unchecked
        if expr.typ == ring.typ
        then matches(config, state, ctx, b, ring, Rewrite.summands(ring, pat), Rewrite.summands(ring, expr), Rewrite.arithmetic(expr), m)
        else Nil

      case (App(fun, inst, typ, args), App(fun_, inst_, typ_, args_)) if fun == fun_ && args.length == args_.length =>
        for
          m1 <- Rewrite.matches(inst, inst_, m)
          m2 <- Rewrite.matches(typ, typ_, m1)
          m3 <- matches(config, state, ctx, b, args, args_, m2)
        yield m3

      case (Lit(value, typ), Lit(value_, typ_)) if value == value_ =>
        Rewrite.matches(typ, typ_, m)

      case (Trace(init, deps, acc, bound, updates), Trace(init_, deps_, acc_, bound_, updates_)) =>
        for
          m1 <- matches(config, state, ctx, b, init, init_, m)
          m2 <- combinator(config, state, ctx, b, deps, bound, deps_, bound_, Map(acc -> acc_), m1): (b_, m) =>
            matches(config, state, ctx, b_, updates, updates_, m)
        yield m2

      case (Maps(deps, bound, updates), Maps(deps_, bound_, updates_)) =>
        combinator(config, state, ctx, b, deps, bound, deps_, bound_, Map(), m): (b_, m) =>
          matches(config, state, ctx, b_, updates, updates_, m)

      case (Invs(deps, bound, body), Invs(deps_, bound_, body_)) =>
        combinator(config, state, ctx, b, deps, bound, deps_, bound_, Map(), m): (b_, m) =>
          matches(config, state, ctx, b_, body, body_, m)

      case _ if pat == expr =>
        List(m)

      // a variable x of the expression with an equation x == e in the context is matched like e,
      // only if the pattern is not a variable, which binds x itself (see above);
      // equations between variables are not followed, since they may be cyclic
      case (_, x: Var) if ctx.eq.get(x).exists(!_.isInstanceOf[Var]) =>
        matches(config, state, ctx, b, pat, ctx.eq(x), m)

      case _ =>
        Nil

  def matches(config: Config, state: State, ctx: Ctx, b: Binding, pats: List[Expr], exprs: List[Expr], m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
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
  // otherwise e.g. x + 1 would match 1 with x = 0, which rewrites literals inside of sums first
  @scala.annotation.targetName("matchesSums")
  def matches(config: Config, state: State, ctx: Ctx, b: Binding, ring: Ring, pats: List[(Boolean, Expr)], exprs: List[(Boolean, Expr)], sum: Boolean, m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    def flexible(summand: (Boolean, Expr)) =
      summand match
        case (_, x: Var) => b.isPattern(x) && !m.vars.contains(x)
        case _           => false

    val (flex, fixed) = pats.partition(flexible)

    def fix(fixed: List[(Boolean, Expr)], exprs: List[(Boolean, Expr)], m: Subst[Type, Expr]): List[(List[(Boolean, Expr)], Subst[Type, Expr])] =
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
          val rest = if sign then exprs else Rewrite.negate(exprs)
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
              m_ <- if sum then matches(config, state, ctx, b, x, ring.lit(util.Rational(0)), m) else Nil
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

  // the variables of the rule among the dependencies, from the values of their bound variables,
  // which must not depend on the accumulator
  def instantiate(config: Config, state: State, ctx: Ctx, b: Binding, zs: List[(Expr, Var)], deps_ : List[Expr], bound_ : List[Var], accs: Set[Var], m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    zs match
      case Nil =>
        List(m)

      case (z: Var, y) :: rest =>
        m.vars.get(y) match
          case Some(value) if (value.free intersect accs).isEmpty =>
            val seq =
              bound_.indexOf(value) match
                case k if k >= 0 =>
                  deps_(k)

                case _ =>
                  val used = (deps_ zip bound_).filter((_, y_) => value.free.contains(y_))
                  val (deps__, bound__) = (if used.isEmpty then (deps_ zip bound_).take(1) else used).unzip
                  Maps(deps__, bound__, List(Upd(True, value)))

            matches(config, state, ctx, b, z, seq, m).flatMap(instantiate(config, state, ctx, b, rest, deps_, bound_, accs, _))

          case _ =>
            Nil

      case _ =>
        Nil

  // each case of the update of the expression is covered by some case of the pattern, whose guard follows from its own
  @scala.annotation.targetName("matchesUpdates")
  def matches(config: Config, state: State, ctx: Ctx, b: Binding, updates: List[Upd], updates_ : List[Upd], m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
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

  // the guard of the pattern matches that of the expression, which instantiates the bound variables of the pattern
  // that do not occur in its result, e.g. b in if b then y + 1, and otherwise it must follow from that of the expression
  def guard(config: Config, state: State, ctx: Ctx, b: Binding, guard_ : Expr, guard: Expr, m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    matches(config, state, ctx, b, guard, guard_, m) match
      case Nil if implies(config, state, ctx, b, guard_, guard, m) => List(m)
      case ms                                                     => ms

  def implies(config: Config, state: State, ctx: Ctx, b: Binding, guard_ : Expr, guard: Expr, m: Subst[Type, Expr]): Boolean =
    if guard == True
    then true
    else
      val su = Subst[Type, Expr](m.params, m.vars ++ b.local)
      val guard__ = su(guard)
      val open = guard__.free.exists(x => b.isPattern(x) && !m.vars.contains(x))
      !open && holds(config, state, ctx, Imp(guard_, guard__))


  // patterns that are sums on Int or Real
  def arithmetic(pat: Expr): Boolean =
    Ring(pat.typ) match
      case Some(ring) =>
        pat match
          case ring.plus(_) | ring.minus(_, _) | ring.uminus(_) => true
          case _                                                => false

      case None =>
        false

  // comparisons on Int and Real as the difference right - left as a normalized polynomial,
  // which is nonnegative, or positive if strict; on Int, left < right is left + 1 <= right, hence never strict,
  // and > and >= are < and <= with the sides swapped
  def comparison(expr: Expr): List[(Ring, Boolean, Poly)] =
    def difference(ring: Ring, left: Expr, right: Expr, offset: Int) =
      (Arith.toPoly(ring, right) - Arith.toPoly(ring, left) - Poly.const(util.Rational(offset))).normalize

    expr match
      case Lt.int(left, right)  => List((Ring.int, false, difference(Ring.int, left, right, 1)))
      case Le.int(left, right)  => List((Ring.int, false, difference(Ring.int, left, right, 0)))
      case Gt.int(left, right)  => List((Ring.int, false, difference(Ring.int, right, left, 1)))
      case Ge.int(left, right)  => List((Ring.int, false, difference(Ring.int, right, left, 0)))
      case Lt.real(left, right) => List((Ring.real, true, difference(Ring.real, left, right, 0)))
      case Le.real(left, right) => List((Ring.real, false, difference(Ring.real, left, right, 0)))
      case Gt.real(left, right) => List((Ring.real, true, difference(Ring.real, right, left, 0)))
      case Ge.real(left, right) => List((Ring.real, false, difference(Ring.real, right, left, 0)))
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
      case ring.plus(args)         => args.flatMap(summands(ring, _))
      case ring.minus(left, right) => summands(ring, left) ++ negate(summands(ring, right))
      case ring.uminus(arg)        => negate(summands(ring, arg))
      case _ if ring.num(expr).exists(_.isZero) => Nil
      case _                       => List((true, expr))

  def negate(summands: List[(Boolean, Expr)]): List[(Boolean, Expr)] =
    for (sign, expr) <- summands
    yield (!sign, expr)

  // the sum of the summands, the positive ones first, which is 0 if there are none
  def sum(ring: Ring, summands: List[(Boolean, Expr)]): Expr =
    val pos = summands.filter(_._1).map(_._2)
    val neg = summands.filterNot(_._1).map(_._2)

    (pos, neg) match
      case (Nil, Nil)        => ring.lit(util.Rational(0))
      case (Nil, n :: ns)    => ns.foldLeft(ring.uminus(n))(ring.minus(_, _))
      case (_, _)            => neg.foldLeft(ring.plus(pos))(ring.minus(_, _))

  // the type parameters of the pattern are instantiated consistently, a single match or none
  def matches(pat: Type, typ: Type, m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    (pat, typ) match
      case (p: Param, _) =>
        m.params.get(p) match
          case Some(t) => if t == typ then List(m) else Nil
          case None    => List(m + (p -> typ))

      case (Sort(con, args), Sort(con_, args_)) if con == con_ =>
        matches(args, args_, m)

      case _ =>
        Nil

  @scala.annotation.targetName("matchesTypes")
  def matches(pats: List[Type], types_ : List[Type], m: Subst[Type, Expr]): List[Subst[Type, Expr]] =
    if pats.length != types_.length
    then Nil
    else
      (pats zip types_).foldLeft(List(m)):
        case (ms, (pat, typ)) => ms.flatMap(matches(pat, typ, _))
