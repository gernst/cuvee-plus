package cuvee.simplify

import cuvee.Error
import cuvee.core._

// a conditional rewrite rule lhs = rhs if cond, whose variables are the free variables of lhs,
// which may be instantiated by arbitrary expressions of the same type,
// and whose type parameters may be instantiated by arbitrary types
case class Rule(lhs: Expr, rhs: Expr, cond: Expr = True):
  Error.report("variables of right hand side or condition do not occur in left hand side", this):
    require((rhs.free ++ cond.free) subsetOf lhs.free)

  Error.report("left hand side of rule is a variable", this):
    require(!lhs.isInstanceOf[Var])

  Error.report("sides of rule have different types", this):
    require(lhs.typ == rhs.typ)

  def vars = lhs.free

// the instantiation of the variables and type parameters of a rule
case class Match(params: Map[Param, Type], vars: Map[Var, Expr]):
  def subst = Subst[Type, Expr](params, vars)

object Match:
  val empty = Match(Map(), Map())

// the variables while matching below the combinators trace, map, and all:
// `vars` are the variables of the rule, `locals` are the bound variables of the pattern that range over dependencies
// that are variables of the rule, which are instantiated like those, `local` relates the other bound variables
// of the pattern to those of the expression, which are `bound`, and which the variables of the rule must not capture
case class Binding(vars: Set[Var], locals: Set[Var], local: Map[Var, Var], bound: Set[Var]):
  def isPattern(x: Var) =
    vars.contains(x) || locals.contains(x)

// a simple rewrite engine: expressions are rewritten innermost first,
// at each position the first rule whose left hand side matches and whose instantiated condition holds is applied,
// and the result is rewritten again, up to a maximal number of steps, which guards against rules that do not terminate;
// matching is syntactic modulo
//   the instantiation of the type parameters of the rules,
//   associativity and commutativity of + and - on Int and Real, and their neutral element 0,
//   the binding structure of the combinators trace, map, and all (see Trace Equation Systems, section 5.2);
// the conditions of rules and the guards of updates are decided by `holds`, by default only if they are syntactically true
class Rewrite(rules: List[Rule], holds: Expr => Boolean = _ == True, steps: Int = 1000):
  var remaining = steps

  def apply(expr: Expr): Expr =
    rewrite(expr)

  def rewrite(expr: Expr): Expr =
    val expr_ = Rewrite.map(expr, rewrite)
    step(expr_) match
      case Some(next) => rewrite(next)
      case None       => expr_

  // a single application of a rule at the top of `expr`
  def step(expr: Expr): Option[Expr] =
    rules.iterator
      .flatMap(rule => apply(rule, expr))
      .nextOption()

  // the first match whose instantiated condition holds
  def apply(rule: Rule, expr: Expr): Option[Expr] =
    val results =
      for
        m <- matches(Binding(rule.vars, Set(), Map(), Set()), rule.lhs, expr, Match.empty)
        su = m.subst
        rhs = su(rule.rhs)
        // steps that do not change the expression are not applications, e.g. x + 0 = x for x without +
        if rhs != expr && holds(su(rule.cond))
      yield rhs

    results.headOption.map: rhs =>
      Error.report("rewriting does not terminate", rule, expr):
        require(remaining > 0)
      remaining -= 1
      cuvee.Debug.info("rewrite", Simplify.show(expr) + "  ~>  " + Simplify.show(rhs))
      rhs

  // all matches of the pattern `pat` to `expr` that extend `m`
  def matches(b: Binding, pat: Expr, expr: Expr, m: Match): LazyList[Match] =
    (pat, expr) match
      case (x: Var, _) if b.local.contains(x) =>
        if expr == b.local(x) then LazyList(m) else LazyList()

      case (x: Var, _) if b.isPattern(x) =>
        m.vars.get(x) match
          case Some(e) =>
            if e == expr then LazyList(m) else LazyList()

          // the variables of the rule must not capture variables bound in the expression
          case None if b.vars.contains(x) && (expr.free intersect b.bound).nonEmpty =>
            LazyList()

          case None =>
            for m_ <- Rewrite.types(x.typ, expr.typ, m).to(LazyList)
            yield m_.copy(vars = m_.vars + (x -> expr))

      case _ if Rewrite.arithmetic(pat) =>
        val Some(ring) = Ring(pat.typ): @unchecked
        if expr.typ == ring.typ
        then sums(b, ring, Rewrite.summands(ring, pat), Rewrite.summands(ring, expr), Rewrite.arithmetic(expr), m)
        else LazyList()

      case (App(fun, inst, typ, args), App(fun_, inst_, typ_, args_)) if fun == fun_ && args.length == args_.length =>
        for
          m1 <- Rewrite.types(inst, inst_, m).to(LazyList)
          m2 <- Rewrite.types(typ, typ_, m1).to(LazyList)
          m3 <- matches(b, args, args_, m2)
        yield m3

      case (Lit(value, typ), Lit(value_, typ_)) if value == value_ =>
        Rewrite.types(typ, typ_, m).to(LazyList)

      case (Trace(init, deps, acc, bound, update), Trace(init_, deps_, acc_, bound_, update_)) =>
        for
          m1 <- matches(b, init, init_, m)
          m2 <- combinator(b, deps, bound, deps_, bound_, Map(acc -> acc_), m1): (b_, m) =>
            cover(b_, update, update_, m)
        yield m2

      case (TraceMap(deps, bound, update), TraceMap(deps_, bound_, update_)) =>
        combinator(b, deps, bound, deps_, bound_, Map(), m): (b_, m) =>
          cover(b_, update, update_, m)

      case (TraceAll(deps, bound, body), TraceAll(deps_, bound_, body_)) =>
        combinator(b, deps, bound, deps_, bound_, Map(), m): (b_, m) =>
          matches(b_, body, body_, m)

      case _ =>
        if pat == expr then LazyList(m) else LazyList()

  def matches(b: Binding, pats: List[Expr], exprs: List[Expr], m: Match): LazyList[Match] =
    (pats, exprs) match
      case (Nil, Nil) =>
        LazyList(m)

      case (pat :: pats_, expr :: exprs_) =>
        matches(b, pat, expr, m).flatMap(matches(b, pats_, exprs_, _))

      case _ =>
        LazyList()

  // sums modulo associativity, commutativity, and the neutral element 0:
  // the summands that are not variables of the pattern are matched to some summand of the same sign first,
  // and the remaining summands are distributed over the variables of the pattern,
  // where all but the last variable take a single summand or none, and the last one takes the rest;
  // variables take the empty sum 0 only if the expression is a sum itself,
  // otherwise e.g. x + 1 would match 1 with x = 0, which rewrites literals inside of sums first
  def sums(b: Binding, ring: Ring, pats: List[(Boolean, Expr)], exprs: List[(Boolean, Expr)], sum: Boolean, m: Match): LazyList[Match] =
    def flexible(summand: (Boolean, Expr)) =
      summand match
        case (_, x: Var) => b.isPattern(x) && !m.vars.contains(x)
        case _           => false

    val (flex, fixed) = pats.partition(flexible)

    def fix(fixed: List[(Boolean, Expr)], exprs: List[(Boolean, Expr)], m: Match): LazyList[(List[(Boolean, Expr)], Match)] =
      fixed match
        case Nil =>
          LazyList((exprs, m))

        case (sign, pat) :: rest =>
          for
            ((sign_, expr), i) <- exprs.zipWithIndex.to(LazyList)
            if sign == sign_
            m_ <- matches(b, pat, expr, m)
            result <- fix(rest, exprs.patch(i, Nil, 1), m_)
          yield result

    def distribute(flex: List[(Boolean, Expr)], exprs: List[(Boolean, Expr)], m: Match): LazyList[Match] =
      flex match
        case Nil =>
          if exprs.isEmpty then LazyList(m) else LazyList()

        case List((sign, x)) if exprs.nonEmpty || sum =>
          val rest = if sign then exprs else Rewrite.negate(exprs)
          matches(b, x, Rewrite.sum(ring, rest), m)

        case List(_) =>
          LazyList()

        case (sign, x) :: flex_ =>
          val single =
            for
              ((sign_, expr), i) <- exprs.zipWithIndex.to(LazyList)
              value = if sign == sign_ then expr else ring.uminus(expr)
              m_ <- matches(b, x, value, m)
              result <- distribute(flex_, exprs.patch(i, Nil, 1), m_)
            yield result

          val none =
            for
              m_ <- if sum then matches(b, x, ring.lit(util.Rational(0)), m) else LazyList()
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
      b: Binding,
      deps: List[Expr],
      bound: List[Var],
      deps_ : List[Expr],
      bound_ : List[Var],
      local: Map[Var, Var],
      m: Match
  )(body: (Binding, Match) => LazyList[Match]): LazyList[Match] =
    val pairs = deps zip bound
    val (zs, es) =
      pairs.partition:
        case (x: Var, _) => b.vars.contains(x)
        case _           => false

    val pairs_ = (deps_ zip bound_).zipWithIndex

    // an injective selection of the dependencies of the expression for those of the pattern that are not variables
    def select(es: List[(Expr, Var)], available: List[((Expr, Var), Int)], m: Match): LazyList[(Map[Var, Var], Match)] =
      es match
        case Nil =>
          LazyList((Map(), m))

        case (dep, y) :: rest =>
          for
            (((dep_, y_), i), k) <- available.zipWithIndex.to(LazyList)
            m1 <- matches(b, dep, dep_, m)
            (local, m2) <- select(rest, available.patch(k, Nil, 1), m1)
          yield (local + (y -> y_), m2)

    for
      (selected, m1) <- select(es, pairs_, m)
      b_ = Binding(b.vars, b.locals ++ zs.map(_._2), b.local ++ local ++ selected, b.bound ++ bound_ ++ local.values)
      m2 <- body(b_, m1)
      m3 <- instantiate(b, zs, deps_, bound_, local.values.toSet, m2)
    yield m3.copy(vars = m3.vars -- zs.map(_._2))

  // the variables of the rule among the dependencies, from the values of their bound variables,
  // which must not depend on the accumulator
  def instantiate(b: Binding, zs: List[(Expr, Var)], deps_ : List[Expr], bound_ : List[Var], accs: Set[Var], m: Match): LazyList[Match] =
    zs match
      case Nil =>
        LazyList(m)

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
                  TraceMap(deps__, bound__, List((True, value)))

            matches(b, z, seq, m).flatMap(instantiate(b, rest, deps_, bound_, accs, _))

          case _ =>
            LazyList()

      case _ =>
        LazyList()

  // each case of the update of the expression is covered by some case of the pattern, whose guard follows from its own
  def cover(b: Binding, update: List[(Expr, Expr)], update_ : List[(Expr, Expr)], m: Match): LazyList[Match] =
    update_ match
      case Nil =>
        LazyList(m)

      case (guard_, result_) :: rest =>
        for
          (guard, result) <- update.to(LazyList)
          m1 <- matches(b, result, result_, m)
          if implies(b, guard_, guard, m1)
          m2 <- cover(b, update, rest, m1)
        yield m2

  def implies(b: Binding, guard_ : Expr, guard: Expr, m: Match): Boolean =
    if guard == True
    then true
    else
      val su = Subst[Type, Expr](m.params, m.vars ++ b.local)
      val guard__ = su(guard)
      val open = guard__.free.exists(x => b.isPattern(x) && !m.vars.contains(x))
      !open && holds(Imp(guard_, guard__))

object Rewrite:
  // rewrite `expr` with `rules` until no rule applies
  def apply(rules: List[Rule], expr: Expr): Expr =
    new Rewrite(rules)(expr)

  def apply(rules: List[Rule], holds: Expr => Boolean): Rewrite =
    new Rewrite(rules, holds)

  // patterns that are sums on Int or Real
  def arithmetic(pat: Expr): Boolean =
    Ring(pat.typ) match
      case Some(ring) =>
        pat match
          case ring.plus(_) | ring.minus(_, _) | ring.uminus(_) => true
          case _                                                => false

      case None =>
        false

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

  // the type parameters of the pattern are instantiated consistently
  def types(pat: Type, typ: Type, m: Match): Option[Match] =
    (pat, typ) match
      case (p: Param, _) =>
        m.params.get(p) match
          case Some(t) => if t == typ then Some(m) else None
          case None    => Some(m.copy(params = m.params + (p -> typ)))

      case (Sort(con, args), Sort(con_, args_)) if con == con_ =>
        types(args, args_, m)

      case _ =>
        None

  @scala.annotation.targetName("typesOfLists")
  def types(pats: List[Type], types_ : List[Type], m: Match): Option[Match] =
    if pats.length != types_.length
    then None
    else
      (pats zip types_).foldLeft(Option(m)):
        case (m, (pat, typ)) => m.flatMap(types(pat, typ, _))

  // apply `f` to the immediate subexpressions
  def map(expr: Expr, f: Expr => Expr): Expr =
    def update(update: List[(Expr, Expr)]) =
      for (guard, result) <- update yield (f(guard), f(result))

    expr match
      case _: Var | _: Lit                      => expr
      case App(fun, inst, typ, args)            => App(fun, inst, typ, args.map(f))
      case Distinct(exprs)                      => Distinct(exprs.map(f))
      case Is(arg, fun)                         => Is(f(arg), fun)
      case As(arg, typ)                         => As(f(arg), typ)
      case Diff(xs, arg)                        => Diff(xs, f(arg))
      case Old(arg)                             => Old(f(arg))
      case Trace(init, deps, acc, bound, upd)   => Trace(f(init), deps.map(f), acc, bound, update(upd))
      case TraceMap(deps, bound, upd)           => TraceMap(deps.map(f), bound, update(upd))
      case TraceAll(deps, bound, body)          => TraceAll(deps.map(f), bound, f(body))
      case Bind(quant, bound, body)             => Bind(quant, bound, f(body))
      case Let(bound, args, body)               => Let(bound, args.map(f), f(body))
