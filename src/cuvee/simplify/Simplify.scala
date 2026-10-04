package cuvee.simplify

import util.Name
import cuvee.pipe.Transform
import cuvee.core._

// contextual simplification of the formulas in assertions and function definitions,
// where each subterm is simplified under the facts known to hold at its position
object Simplify extends Transform:
  // debug output is printed with the printer of the configuration
  def apply(config: cuvee.Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val ctx = Ctx.empty

    for cmd <- cmds
    yield simplify(config, state, ctx, cmd)

  // `ctx` is an empty context, which provides the rewrite rules
  def simplify(config: cuvee.Config, state: State, ctx: Ctx, cmd: Cmd): Cmd =
    cmd match
      case Assert(justify, params, phi, attrs) =>
        Assert(justify, params, simplify(config, state, ctx.copy(polarity = Some(true)), phi), attrs)

      case DefineFun(fun, body, attrs) =>
        DefineFun(fun, simplify(config, state, ctx, body), attrs)

      case DeclareProc(proc, attrs) =>
        DeclareProc(proc, simplify(config, state, ctx, attrs))

      case DefineProc(proc, body, attrs) =>
        DefineProc(proc, simplify(config, state, ctx, body), simplify(config, state, ctx, attrs))

      case _ =>
        cmd

  // the formulas and terms in attributes, e.g. contracts and invariants, are simplified without context
  def simplify(config: cuvee.Config, state: State, ctx: Ctx, attrs: Attrs): Attrs =
    val attrs_ =
      for (kw, arg) <- attrs.attrs
      yield arg match
        case Some(expr: Expr) => kw -> Some(simplify(config, state, ctx, expr))
        case _                => kw -> arg

    Attrs(attrs_)

  // programs are simplified statement by statement, where the expressions are simplified without context,
  // since the facts known before an assignment may not hold afterwards;
  // branches and loops with constant tests are reduced, and statements without effect are dropped
  def simplify(config: cuvee.Config, state: State, ctx: Ctx, prog: Prog): Prog =
    val e = (expr: Expr) => simplify(config, state, ctx, expr)
    val p = (prog: Prog) => simplify(config, state, ctx, prog)

    prog match
      case Break | Continue | Return =>
        prog

      case Spec(xs, pre, post) =>
        Spec(xs, e(pre), e(post))

      case Assign(lhs, rhs) =>
        val pairs = (lhs zip rhs.map(e)).filterNot((x, rhs_) => x == rhs_)
        Assign(pairs.map(_._1), pairs.map(_._2))

      case Call(name, args, res) =>
        Call(name, args.map(e), res)

      // nested blocks without locals are merged, statements without effect are dropped
      case Block(locals, progs) =>
        val progs_ =
          progs.map(p).flatMap:
            case Block(Nil, inner)                  => inner
            case Assign(Nil, Nil) | Spec(Nil, True, True) => Nil
            case prog_                              => List(prog_)
        Block(locals.filter(x => progs_.exists(_.free.contains(x))), progs_)

      case Choice(progs) =>
        Choice(progs.map(p))

      case If(test, left, right) =>
        e(test) match
          case True  => p(left)
          case False => p(right)
          case test_ => If(test_, p(left), p(right))

      case While(test, body, attrs) =>
        e(test) match
          case False => Block(Nil, Nil)
          case test_ => While(test_, p(body), simplify(config, state, ctx, attrs))

      case Iter(body, attrs) =>
        Iter(p(body), simplify(config, state, ctx, attrs))

      case Ode(xs, rhs, dom, attrs) =>
        Ode(xs, rhs.map(e), e(dom), simplify(config, state, ctx, attrs))

      case Par(calls) =>
        Par(for Call(name, args, res) <- calls yield Call(name, args.map(e), res))

  // simplify `expr` assuming that all facts in `ctx` hold
  // by repeated rounds of simplification until a fixpoint is reached,
  // a formula that is known from the context is replaced by its truth value;
  // after each round, a rewrite rule of the context is applied at the top, whose subterms are simplified already
  def simplify(config: cuvee.Config, state: State, ctx: Ctx, expr: Expr): Expr =
    ctx.lookup(expr) match
      case Some(true)  => True
      case Some(false) => False
      case None =>
        val once_ = once(config, state, ctx, expr)
        if once_ != expr
        then cuvee.Debug.info("simplify", show(config.printer, expr) + "  ~>  " + show(config.printer, once_))

        val expr_ = rewrite(config, state, ctx, once_)
        if expr_ == expr
        then expr
        else simplify(config, state, ctx, expr_)

  // expressions in debug output, on a single line
  def show(printer: cuvee.pipe.Printer, expr: Expr): String =
    printer.lines(expr).map(_.trim).mkString(" ")

  // a single step with the rewrite rules of the context at the top of `expr`,
  // where the conditions of the rules are decided by simplification in the context (see Rewrite)
  def rewrite(config: cuvee.Config, state: State, ctx: Ctx, expr: Expr): Expr =
    Rewrite.step(config, state, ctx, expr).getOrElse(expr)

  // a single round of simplification, dispatching on the builtin functions,
  // subterms are simplified first, where ite and the boolean connectives
  // extend the context by the facts known at the position of each subterm,
  // negation and the premise of implication flip the polarity,
  // and the arguments of other functions have none
  def once(config: cuvee.Config, state: State, ctx: Ctx, expr: Expr): Expr =
    expr match
      case x: Var =>
        var_(config, state, ctx, x)

      case _: Lit | True | False =>
        expr

      case Eq(left, right) =>
        val left_ = simplify(config, state, ctx.neutral, left)
        val right_ = simplify(config, state, ctx.neutral, right)
        eq_(config, state, ctx, left_, right_)

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

  // simplify each of `phis` assuming the others, which hold if `pos` (conjunction)
  // and do not hold otherwise (disjunction);
  // propositions in `done` are already processed (in reverse) and assumed in their simplified form,
  // otherwise e.g. both copies in `a and a` would simplify to true
  def nary(config: cuvee.Config, state: State, ctx: Ctx, done: List[Expr], phis: List[Expr], pos: Boolean): List[Expr] =
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
  def arith(config: cuvee.Config, state: State, ctx: Ctx, expr: Expr): Expr =
    Ring(expr.typ) match
      case Some(ring) => poly(config, state, ctx, ring, expr).normalize.toExpr(ring)
      case None       => simplify(config, state, ctx, expr)

  // simplify an integer- or real-valued term into a polynomial (not normalized):
  // descend through +, -, * and literals, simplify the leaves,
  // which may in turn become arithmetic expressions, and combine the results;
  // on Real, division by a term that simplifies to a nonzero literal is multiplication by its inverse
  def poly(config: cuvee.Config, state: State, ctx: Ctx, ring: Ring, expr: Expr): Poly =
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
  def var_(config: cuvee.Config, state: State, ctx: Ctx, x: Var): Expr =
    ctx.su.vars.get(x) match
      case Some(y) => y
      case None    => x

  def eq_(config: cuvee.Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
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

  // false if two of the expressions are equal, true if all of them are pairwise different,
  // e.g. literals, two expressions are distinct exactly if they are not equal
  def distinct(config: cuvee.Config, state: State, ctx: Ctx, exprs: List[Expr]): Expr =
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
  def is(config: cuvee.Config, state: State, ctx: Ctx, arg: Expr, fun: Fun): Expr =
    constr(config, state, arg) match
      case Some(constr) if constr.name == fun.name => True
      case Some(constr)                            => False
      case None                                    => Is(arg, fun)

  // the constructor that `expr` is built by, looking through type annotations
  def constr(config: cuvee.Config, state: State, expr: Expr): Option[Fun] =
    expr match
      case As(expr_, _) =>
        constr(config, state, expr_)

      case App(fun, _, _, _) if state.constrs contains fun.name =>
        Some(fun)

      case _ =>
        None

  def ite(config: cuvee.Config, state: State, ctx: Ctx, test: Expr, left: Expr, right: Expr): Expr =
    (test, left, right) match
      case (True, _, _)          => left
      case (False, _, _)         => right
      case _ if left == right    => left
      case (_, True, False)      => test
      case (_, False, True)      => Not(test)
      case _                     => Ite(test, left, right)

  // read over write
  def select(config: cuvee.Config, state: State, ctx: Ctx, base: Expr, index: Expr): Expr =
    base match
      case Store(_, index_, value) if index_ == index =>
        value

      case Store(base_, index_, _) if eq_(config, state, ctx, index_, index) == False =>
        Select(base_, index)

      case _ =>
        Select(base, index)

  def store(config: cuvee.Config, state: State, ctx: Ctx, base: Expr, index: Expr, value: Expr): Expr =
    (base, value) match
      // overwritten
      case (Store(base_, index_, _), _) if index_ == index =>
        Store(base_, index, value)

      // writes back what is already stored
      case (_, Select(base_, index_)) if base_ == base && index_ == index =>
        base

      case _ =>
        Store(base, index, value)

  def not(config: cuvee.Config, state: State, ctx: Ctx, phi: Expr): Expr =
    phi match
      case True     => False
      case False    => True
      case Not(psi) => psi
      case _        => Not(phi)

  def imp(config: cuvee.Config, state: State, ctx: Ctx, phi: Expr, psi: Expr): Expr =
    (phi, psi) match
      case (True, _)          => psi
      case (False, _)         => True
      case (_, True)          => True
      case (_, False)         => Not(phi)
      case _ if phi == psi    => True
      case _                  => Imp(phi, psi)

  // flatten nested conjunctions, drop true and duplicates,
  // false or a complementary pair makes the whole conjunction false
  def and(config: cuvee.Config, state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.flatMap(And.flattenStrong).distinct
    if phis_.contains(False) || phis_.exists(phi => phis_ contains Not(phi))
    then False
    else And(phis_)

  // dual to and
  def or(config: cuvee.Config, state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.flatMap(Or.flattenStrong).distinct
    if phis_.contains(True) || phis_.exists(phi => phis_ contains Not(phi))
    then True
    else Or(phis_)

  // SMT-LIB semantics: for n != 0, m = n * (m div n) + (m mod n) with 0 <= m mod n < |n|,
  // division by zero is unspecified and therefore left alone
  def div(config: cuvee.Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
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

  def mod(config: cuvee.Config, state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
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
  def diff(config: cuvee.Config, state: State, xs: List[Var], expr: Expr): Expr =
    val d = (arg: Expr) => diff(config, state, xs, arg)

    expr match
      case _ if expr.typ == Sort.real && (expr.free intersect xs.toSet).isEmpty =>
        Zero.real

      case x: Var if x.typ == Sort.real =>
        x.primed

      case UMinus.real(arg) =>
        UMinus.real(d(arg))

      case Plus.real(args) =>
        Plus.real(args.map(d))

      case Minus.real(left, right) =>
        Minus.real(d(left), d(right))

      // (a * b * c)' = a' * b * c + a * b' * c + a * b * c'
      case Times.real(args) =>
        val summands =
          for i <- args.indices.toList
          yield Times.real(args.updated(i, d(args(i))))
        Plus.real(summands)

      case Lt.real(left, right) =>
        Le.real(d(left), d(right))

      case Le.real(left, right) =>
        Le.real(d(left), d(right))

      case And(phis) =>
        And(phis.map(d))

      case _ =>
        Diff(xs, expr)

  // the difference right - left of the sides of a comparison as a normalized polynomial
  def difference(config: cuvee.Config, state: State, ctx: Ctx, ring: Ring, left: Expr, right: Expr): Poly =
    val left_ = poly(config, state, ctx, ring, left)
    val right_ = poly(config, state, ctx, ring, right)
    (right_ - left_).normalize

  // comparisons 0 < p and 0 <= p on Int or Real, built by `op`, are constants if p is,
  // otherwise they are re-arranged so that both sides have positive coefficients only,
  // e.g. 0 < y - x + 1 becomes x < y + 1
  def lt(config: cuvee.Config, state: State, ctx: Ctx, ring: Ring, op: Sugar.binary, poly: Poly): Expr =
    if poly.monos.isEmpty
    then if poly.const.isPositive then True else False
    else
      val (left, right) = poly.sides
      op(left.toExpr(ring), right.toExpr(ring))

  def le(config: cuvee.Config, state: State, ctx: Ctx, ring: Ring, op: Sugar.binary, poly: Poly): Expr =
    if poly.monos.isEmpty
    then if poly.const.isNegative then False else True
    else
      val (left, right) = poly.sides
      op(left.toExpr(ring), right.toExpr(ring))

  // applications of other functions, e.g. user-defined ones
  def app(config: cuvee.Config, state: State, ctx: Ctx, fun: Fun, inst: List[Type], typ: Type, args: List[Expr]): Expr =
    App(fun, inst, typ, args)

  // unused bound variables are dropped,
  // the binder vanishes when none remain (sorts are nonempty in SMT-LIB)
  def bind(config: cuvee.Config, state: State, ctx: Ctx, quant: Name, bound: List[Var], body: Expr): Expr =
    val bound_ = bound.filter(body.free.contains)
    if bound_.isEmpty
    then body
    else Bind(quant, bound_, body)

  // unused bindings are dropped
  def let(config: cuvee.Config, state: State, ctx: Ctx, bound: List[Var], args: List[Expr], body: Expr): Expr =
    val pairs = (bound zip args).filter((x, _) => body.free contains x)
    if pairs.isEmpty
    then body
    else Let(pairs.map(_._1), pairs.map(_._2), body)
