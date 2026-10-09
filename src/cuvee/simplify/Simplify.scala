package cuvee.simplify

import util.Name
import cuvee.Debug
import cuvee.Error
import cuvee.Config
import cuvee.pipe.Transform
import cuvee.core._
import util.Rational
import util.disjoint
import util.intersects

// contextual simplification of the formulas in assertions and function definitions,
// where each subterm is simplified under the facts known to hold at its position
object Simplify extends Transform:
  // the assertions and lemmas with the attribute :rw so far are rewrite rules, which are kept as they are,
  // the other commands are simplified with these rules, each with a fresh number of rewrite steps,
  // where axioms, goals, and lemmas that simplify to true are dropped, since they state nothing;
  // debug output is printed with the printer of the configuration
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val rules = Rules.from(state, prefix ++ cmds)

    for
      cmd <- cmds
      cmd_ = if cmd.isRule then cmd else simplify(config, state, Context.empty.withRules(rules), cmd)
      if !isTrivial(cmd_)
    yield cmd_

  def isTrivial(cmd: Cmd) =
    cmd match
      case Assert(_, _, True, _) => true
      case _                     => false

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

        case DeclareProc(proc, attrs) =>
          DeclareProc(proc, simplify(config, state, ctx, attrs))

        case DefineProc(proc, body, attrs) =>
          DefineProc(proc, simplify(config, state, ctx, body), simplify(config, state, ctx, attrs))

        case _ =>
          cmd
    catch
      case _: StackOverflowError if ctx.rules.nonEmpty =>
        Error.raise("rewriting does not terminate")

  // the formulas and terms in attributes, e.g. contracts and invariants, are simplified without context
  def simplify(config: Config, state: State, ctx: Context, attrs: Attrs): Attrs =
    attrs.map(simplify(config, state, ctx, _))

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
  // after each round, a rewrite rule of the context is applied at the top, whose subterms are simplified already
  def simplify(config: Config, state: State, ctx: Context, expr: Expr): Expr =
    if implied(config, state, ctx, expr)
    then True
    else if denied(config, state, ctx, expr)
    then False
    else
      val once_ = once(config, state, ctx, expr)
      if once_ != expr
      then Debug.step("simplify", show(config.output.printer, expr), show(config.output.printer, once_))

      val expr_ = rewrite(config, state, ctx, once_)
      if expr_ == expr
      then expr
      else simplify(config, state, ctx, expr_)

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

  // expressions in debug output, on a single line
  def show(printer: cuvee.pipe.Printer, rule: Rule): String =
    printer.lines(rule).map(_.trim).mkString(" ")

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
      case Eq(x: Var, Trace(init, deps, acc, bound, update)) =>
        val left_ = simplify(config, state, ctx.neutral, x)
        val init_ = simplify(config, state, ctx.neutral, init)
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (vars_, re) = Subst.rename(acc :: bound, ctx.free)
        val inner = combinator(config, state, ctx.bind(List(vars_.head)).copy(self = Some((Butlast(x), vars_.head))), deps_, vars_.tail)
        val update_ = simplify(config, state, inner, re(update))
        val right_ = trace(config, state, ctx.neutral, init_, deps_, vars_.head, vars_.tail, update_)
        eq_(config, state, ctx, left_, rewrite(config, state, ctx.neutral, right_, Some(x)))

      case Eq(y: Var, Maps(deps, bound, update)) =>
        val left_ = simplify(config, state, ctx.neutral, y)
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val update_ = simplify(config, state, combinator(config, state, ctx.copy(self = Some((y, re(update)))), deps_, bound_), re(update))
        val right_ = maps(config, state, ctx.neutral, deps_, bound_, update_)
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

      case Diff(xs, arg) =>
        val arg_ = simplify(config, state, ctx.neutral, arg)
        diff(config, state, xs, arg_)

      case Old(arg) =>
        Old(simplify(config, state, ctx.neutral, arg))

      case As(arg, typ) =>
        val arg_ = simplify(config, state, ctx, arg)
        As(arg_, typ)

      // the branches have no polarity, since the context does not record the other branch (see Context.neutral)
      case Ite(test, left, right) =>
        val test_ = simplify(config, state, ctx.neutral, test)
        val left_ = simplify(config, state, ctx.neutral.assume(List(test_), Nil), left)
        // the negated test, which may be stronger in the context, e.g. a strict comparison (see not)
        val right_ = simplify(config, state, ctx.neutral.assume(List(not(config, state, ctx, test_)), Nil), right)
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
        val phi_ = simplify(config, state, ctx.flip.assume(Nil, List(psi)), phi)
        val psi_ = simplify(config, state, ctx.assume(List(phi_), Nil), psi)
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

      // bound variables are renamed apart from the context before entering the body,
      // naturals that occur as integers only become integers within their range (see integers)
      case All(bound, body) =>
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val (bound__, ranges, body__) = integers(bound_, re(body))
        val body___ = if ranges.isEmpty then body__ else Imp(And(ranges), body__)
        val body_ = simplify(config, state, ctx.forall(bound__), body___)
        all(config, state, ctx, bound__, body_)

      case Ex(bound, body) =>
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val (bound__, ranges, body__) = integers(bound_, re(body))
        val body_ = simplify(config, state, ctx.exists(bound__), And(ranges :+ body__))
        ex(config, state, ctx, bound__, body_)

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
        match_(config, state, ctx, arg_, cases.map(this.cases(config, state, ctx, _)))

      // the cases like those of match, the function is not unfolded
      case Rec(fun, cases) =>
        rec(config, state, ctx, fun, cases.map(this.cases(config, state, ctx, _)))

      // the combinators bind the accumulator and the variables for the dependencies like quantifiers,
      // their updates and bodies assume the invariants of the context over the same dependencies (see combinator)
      case Trace(init, deps, acc, bound, update) =>
        val init_ = simplify(config, state, ctx.neutral, init)
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (vars_, re) = Subst.rename(acc :: bound, ctx.free)
        val update_ = simplify(config, state, combinator(config, state, ctx.bind(List(vars_.head)), deps_, vars_.tail), re(update))
        trace(config, state, ctx, init_, deps_, vars_.head, vars_.tail, update_)

      case Maps(deps, bound, update) =>
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val update_ = simplify(config, state, combinator(config, state, ctx, deps_, bound_), re(update))
        maps(config, state, ctx, deps_, bound_, update_)

      // the guards of the cases are simplified, cases whose guard is false are dropped,
      // and the results are simplified assuming their guard and, since the guards are disjoint, that the others are false;
      // not so the guards themselves, which would become true, as the guards are also complete
      case Eps(updates) =>
        val updates_ =
          for
            Upd(cond, rhs) <- updates
            cond_ = simplify(config, state, ctx.neutral, cond)
            if cond_ != False
          yield Upd(cond_, rhs)

        val updates__ =
          for (Upd(cond_, rhs), i) <- updates_.zipWithIndex
          yield
            val others = updates_.guards.patch(i, Nil, 1)
            upd(config, state, ctx, cond_, simplify(config, state, ctx.neutral.assume(List(cond_), others), rhs))

        eps(config, state, ctx, updates__)

      // the body holds for all values of the dependencies, like the body of a universal quantifier,
      // but without polarity, since the dependencies are not recorded in the context
      case Invs(deps, bound, body) =>
        val deps_ = simplify(config, state, ctx.neutral, deps)
        val (bound_, re) = Subst.rename(bound, ctx.free)
        val body_ = simplify(config, state, combinator(config, state, ctx, deps_, bound_), re(body))
        invs(config, state, ctx, deps_, bound_, body_)

  // the context of the updates and bodies of combinators, which binds the variables for the dependencies,
  // and which assumes the invariants of the context over the same dependencies and the iterations of loops;
  // ctx.self is the dependency that the combinator defines and its value in the update, if known (see once)
  // built once per command for the same outer context (see Context.combinators)
  def combinator(config: Config, state: State, ctx: Context, deps: List[Expr], bound: List[Var]): Context =
    val key = (deps, bound, ctx.key)
    ctx.combinators.value.get(key) match
      case Some(inner) =>
        inner

      case None =>
        val inner = ctx.neutral.bind(bound).assume(invariants(ctx, deps, bound) ++ iterations(config, state, ctx, deps, bound), Nil)
        ctx.combinators := ctx.combinators.value + (key -> inner)
        inner

  // the bodies of the invariants among the assumptions whose dependencies are among `deps` and `self`,
  // with their bound variables renamed to those of the corresponding dependencies in `bound`, or to the value of ctx.self,
  // which hold at each position of the dependencies, hence also for the values bound there;
  // the dependencies of a combinator have equal length, such that the positions coincide
  def invariants(ctx: Context, deps: List[Expr], bound: List[Var]): List[Expr] =
    val values = (deps zip bound).toMap[Expr, Expr] ++ ctx.self
    for
      case Invs(deps_, bound_, body) <- ctx.facts.assms
      if deps_.forall(values.contains)
    yield
      val re = Subst.from(bound_, deps_.map(values))
      re(body)

  // if the first dependency counts the iterations of a loop, ⌊counter(0, 1, n)⌋ bound to k (see Rewrite.iterations),
  // then 0 <= k < integer(n), since the loop exits when k == n, and the variable z bound to each other dependency ⌊Z⌋
  // is its value in iteration k, i.e., z == earlier(natural(k), ⌊Z⌋), which is simplified within the range,
  // e.g. z == k for ⌊Z⌋ with Z == counter(0, 1, n), which then bounds z as well
  def iterations(config: Config, state: State, ctx: Context, deps: List[Expr], bound: List[Var]): List[Expr] =
    (deps, bound) match
      case (Butlast(ctx.↑(Counter(Ints.zero, Ints.one, n))) :: deps_, k :: bound_) =>
        val ctx_ = ctx.neutral.bind(bound)
        val bounds = List(Ints.le(Ints.zero, k), Ints.lt(k, Nats.integer(n)))
        val range = simplify(config, state, ctx_, bounds)
        val inside = ctx_.assume(range, Nil)
        val values = (deps_ zip bound_).map((dep, z) => Eq(z, simplify(config, state, inside, Earlier(Nats.natural(k), dep))))
        range ++ values

      case _ =>
        Nil

  // the variables of the pattern are renamed apart like bound variables, and the body assumes the condition,
  // without polarity, since the context does not record the argument
  def cases(config: Config, state: State, ctx: Context, cs: Case): Case =
    val Case(pat, body, cond) = cs
    val (bound_, re) = Subst.rename(pat.free.toList, ctx.free)
    val cond_ = simplify(config, state, ctx.neutral.bind(bound_), re(cond))
    val body_ = simplify(config, state, ctx.neutral.bind(bound_).assume(List(cond_), Nil), re(body))
    case_(config, state, ctx, re(pat), body_, cond_)

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
          then ctx.assume(others, Nil)
          else ctx.assume(Nil, others)
        val phi_ = simplify(config, state, ctx_, phi)
        nary(config, state, ctx, phi_ :: done, rest, pos)

  // simplify an integer- or real-valued term into the normal form of polynomials,
  // terms of other types, e.g. of defined sorts, are simplified only
  def arith(config: Config, state: State, ctx: Context, expr: Expr): Expr =
    Ring(expr.typ) match
      case Some(ring) => 
        val poly_ = poly(config, state, ctx, ring, expr)
        val norm_ = poly_.normalize
        val expr_ = norm_.toExpr(ring)
        expr_

      case None       => 
        simplify(config, state, ctx, expr)

  // simplify an integer- or real-valued term into a polynomial (not normalized):
  // descend through +, -, * and literals, simplify the leaves,
  // which may in turn become arithmetic expressions, and combine the results;
  // on Real, division by a term that simplifies to a nonzero literal is multiplication by its inverse;
  // variables with the solution of an arithmetic equation in the context are inlined (see Chains.solved),
  // unless the solution depends on the variable through the equations of the context, which would loop
  def poly(config: Config, state: State, ctx: Context, ring: Ring, expr: Expr): Poly =
    expr match
      case ring.num(n: BigInt) =>
        Poly.const(Rational(n))

      case ring.num(n: Rational) =>
        Poly.const(n)

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

      case Reals.div(left, right) =>
        val left_ = poly(config, state, ctx, ring, left)
        val right_ = simplify(config, state, ctx, right)
        right_ match
          case ring.num(r: Rational) if !r.isZero => left_ * (Rational(1) / r)
          case _                                  => Poly.atom(Reals.div(left_.normalize.toExpr(ring), right_))

      case _ =>
        simplify(config, state, ctx, expr) match
          case x: Var if ctx.chains.solved.get(x).exists(ctx.chains.acyclic(x, _)) =>
            poly(config, state, ctx, ring, ctx.chains.solved(x))

          case expr_ =>
            Arith.toPoly(ring, expr_)

  // variables known to be equal to another one or to a literal are replaced
  def var_(config: Config, state: State, ctx: Context, x: Var): Expr =
    ctx.chains.replace.get(x) match
      case Some(e) => e
      case None    => x

  def eq_(config: Config, state: State, ctx: Context, left: Expr, right: Expr): Expr =
    (left, right) match
      case _ if left == right =>
        True

      // variables with the same definition among the assumptions, or a variable and its definition (see Context.↑)
      case (ctx.↑(left_), ctx.↑(right_)) if left_ == right_ =>
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

      // the coefficients and the constant of a polynomial are taken modulo n, e.g. (2 * x + 3) % 2 is 1
      case (_, Lit(n: BigInt, _)) if n != 0 =>
        val poly = Arith.toPoly(Ints.ring, left)
        val reduced = poly.modulo(n)
        if reduced != poly.normalize
        then mod(config, state, ctx, reduced.toExpr(Ints.ring), right)
        else Ints.mod(left, right)

      case _ =>
        Ints.mod(left, right)

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
    val left_ = poly(config, state, ctx, ring, left)
    val right_ = poly(config, state, ctx, ring, right)
    (right_ - left_).normalize.primitive

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
    else if poly.solution((x, rest) => point(ctx, x, rest.toExpr(ring))).nonEmpty
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

  // earlier moves inward: into maps, whose element j is its update for the elements j of the dependencies,
  // into both branches of ite, and into the body of let, whose bound variables are renamed apart from j
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

      case expr =>
        expr

  // a bound natural n that occurs only as its value integer(n) is an integer variable of the same name within its range
  // 0 <= n, such that arithmetic reasons about it, e.g. forall n: Nat :: integer(n) != 10 is false for n == 10;
  // the bound variables, the ranges, and the body with the integers
  def integers(bound: List[Var], body: Expr): (List[Var], List[Expr], Expr) =
    val naturals = bound.filter(x => x.typ == Sort.nat && asInteger(x, body))
    val ints = naturals.map(x => Var(x.name, Sort.int))
    val su = (naturals zip ints).toMap
    val bound_ = bound.map(x => su.getOrElse(x, x))
    (bound_, ints.map(Ints.le(Ints.zero, _)), (naturals zip ints).foldLeft(body)((expr, x) => integer(x._1, x._2, expr)))

  // whether `x` occurs in `expr` only as integer(x)
  def asInteger(x: Var, expr: Expr): Boolean =
    expr match
      case Nats.integer(`x`) => true
      case `x`               => false
      case _ =>
        var only = true
        expr.map { arg => only = only && asInteger(x, arg); arg }
        only

  // `expr` with integer(x) replaced by `m`
  def integer(x: Var, m: Var, expr: Expr): Expr =
    expr match
      case Nats.integer(`x`) => m
      case _                 => expr.map(integer(x, m, _))

  // forall distributes over and, where each conjunct binds the variables that it uses
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

  // eta reduction, the lambda that selects the elements of an array is that array,
  // and the lambda that applies a function value to its variables is that function value
  def lam(config: Config, state: State, ctx: Context, bound: List[Var], body: Expr, typ: Type): Expr =
    (bound, body) match
      case (List(x), Select(base, index)) if index == x && !base.free.contains(x) =>
        base

      case (_, Apply(f, args)) if args == bound && (bound disjoint f.free) =>
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
  // and a single case is its result, since the guards are complete,
  // e.g. case b => y case c => y is y, which is a trace that keeps its value
  def eps(config: Config, state: State, ctx: Context, updates: List[Upd]): Expr =
    val merged =
      Eps.flatten(updates).foldLeft(List.empty[Upd]): (merged, update) =>
        merged.indexWhere(other => eq_(config, state, ctx.neutral, other.rhs, update.rhs) == True) match
          case -1 =>
            merged :+ update

          case i =>
            val Upd(cond, rhs) = merged(i)
            merged.updated(i, Upd(or(config, state, ctx.neutral, List(cond, update.cond)), rhs))

    merged match
      case List(Upd(_, rhs)) => rhs
      case _                 => Eps(merged)

  def trace(config: Config, state: State, ctx: Context, init: Expr, deps: List[Expr], acc: Var, bound: List[Var], update: Expr): Expr =
    val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, update.free - acc)
    Trace(init, deps_, acc, bound_, re(update))

  def maps(config: Config, state: State, ctx: Context, deps: List[Expr], bound: List[Var], update: Expr): Expr =
    val (deps_, bound_, re) = this.deps(config, state, ctx, deps, bound, update.free)
    Maps(deps_, bound_, re(update))

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

  // programs are simplified statement by statement, where the expressions are simplified without context,
  // since the facts known before an assignment may not hold afterwards;
  // the helpers below normalize their own constructor, as those of expressions
  def simplify(config: Config, state: State, ctx: Context, prog: Prog): Prog =
    prog match
      case Break | Continue | Return =>
        prog

      case Spec(xs, pre, post) =>
        val pre_ = simplify(config, state, ctx, pre)
        val post_ = simplify(config, state, ctx, post)
        spec(config, state, ctx, xs, pre_, post_)

      case Assign(lhs, rhs) =>
        val rhs_ = simplify(config, state, ctx, rhs)
        assign(config, state, ctx, lhs, rhs_)

      case Call(name, args, res) =>
        val args_ = simplify(config, state, ctx, args)
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
        val rhs_ = simplify(config, state, ctx, rhs)
        val dom_ = simplify(config, state, ctx, dom)
        val attrs_ = simplify(config, state, ctx, attrs)
        ode(config, state, ctx, time, xs, rhs_, dom_, attrs_)

      case Par(progs) =>
        val progs_ = progs.map(simplify(config, state, ctx, _))
        par(config, state, ctx, progs_)

  // havoc of no variables under the trivial contract has no effect
  def spec(config: Config, state: State, ctx: Context, xs: List[Var], pre: Expr, post: Expr): Prog =
    (xs, pre, post) match
      case (Nil, True, True) => Skip
      case _                 => Spec(xs, pre, post)

  // assignments of variables to themselves are dropped, and no assignment has no effect
  def assign(config: Config, state: State, ctx: Context, lhs: List[Var], rhs: List[Expr]): Prog =
    val (lhs_, rhs_) = (lhs zip rhs).filterNot((x, e) => x == e).unzip
    if lhs_.isEmpty
    then Skip
    else Assign(lhs_, rhs_)

  def call(config: Config, state: State, ctx: Context, name: Name, args: List[Expr], res: List[Var]): Prog =
    Call(name, args, res)

  // nested blocks are merged, which drops Skip, the empty block, and whose locals are hoisted unless that captures
  // variables of the other statements; statements after a jump and locals that are not used are dropped;
  // a block of a single statement without locals is that statement
  def block(config: Config, state: State, ctx: Context, locals: List[Var], progs: List[Prog]): Prog =
    def flatten(locals: List[Var], done: List[Prog], progs: List[Prog]): (List[Var], List[Prog]) =
      progs match
        case Nil =>
          (locals, done)

        case (jump @ (Break | Continue | Return)) :: _ =>
          (locals, done :+ jump)

        case Block(inner, progs_) :: rest
            if (inner disjoint locals.toSet) && !(done ++ rest).exists(p => inner intersects p.free) =>
          flatten(locals ++ inner, done, progs_ ++ rest)

        case prog :: rest =>
          flatten(locals, done :+ prog, rest)

    val (locals_, progs_) = flatten(locals, Nil, progs)
    val used = locals_.filter(x => progs_.exists(_.free.contains(x)))
    (used, progs_) match
      case (Nil, List(prog)) => prog
      case _                 => Block(used, progs_)

  // nested choices are merged, duplicates are dropped, and a choice of a single statement is that statement
  def choice(config: Config, state: State, ctx: Context, progs: List[Prog]): Prog =
    Choice.flatten(progs).distinct match
      case List(prog) => prog
      case progs__    => Choice(progs__)

  // constant tests select a branch, equal branches make the test irrelevant,
  // and a negated test swaps the branches
  def if_(config: Config, state: State, ctx: Context, test: Expr, left: Prog, right: Prog): Prog =
    test match
      case True               => left
      case False              => right
      case _ if left == right => left
      case Not(test_)         => If(test_, right, left)
      case _                  => If(test, left, right)

  // a loop that is never entered has no effect
  def while_(config: Config, state: State, ctx: Context, test: Expr, body: Prog, attrs: Attrs): Prog =
    test match
      case False => Skip
      case _     => While(test, body, attrs)

  def iter(config: Config, state: State, ctx: Context, body: Prog, attrs: Attrs): Prog =
    Iter(body, attrs)

  def ode(config: Config, state: State, ctx: Context, time: Var, xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs): Prog =
    Ode(time, xs, rhs, dom, attrs)

  def par(config: Config, state: State, ctx: Context, progs: List[Prog]): Prog =
    Par(progs)
