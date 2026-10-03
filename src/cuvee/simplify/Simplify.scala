package cuvee.simplify

import util.Name
import cuvee.pipe.Transform
import cuvee.core._

// contextual simplification of the formulas in assertions and function definitions,
// where each subterm is simplified under the facts known to hold at its position
object Simplify extends Transform:
  def apply(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State): List[Cmd] =
    for cmd <- cmds
    yield simplify(state, cmd)

  def simplify(state: State, cmd: Cmd): Cmd =
    cmd match
      case Assert(justify, params, phi, attrs) =>
        Assert(justify, params, simplify(state, Ctx.pos, phi), attrs)

      case DefineFun(fun, body, attrs) =>
        DefineFun(fun, simplify(state, Ctx.empty, body), attrs)

      case _ =>
        cmd

  // simplify `expr` assuming that all facts in `ctx` hold
  // by repeated rounds of simplification until a fixpoint is reached,
  // a formula that is known from the context is replaced by its truth value
  def simplify(state: State, ctx: Ctx, expr: Expr): Expr =
    ctx.lookup(expr) match
      case Some(true)  => True
      case Some(false) => False
      case None =>
        val expr_ = once(state, ctx, expr)
        if expr_ == expr
        then expr
        else simplify(state, ctx, expr_)

  // a single round of simplification, dispatching on the builtin functions,
  // subterms are simplified first, where ite and the boolean connectives
  // extend the context by the facts known at the position of each subterm,
  // negation and the premise of implication flip the polarity,
  // and the arguments of other functions have none
  def once(state: State, ctx: Ctx, expr: Expr): Expr =
    expr match
      case x: Var =>
        var_(state, ctx, x)

      case _: Lit | True | False =>
        expr

      case Eq(left, right) =>
        val left_ = simplify(state, ctx.neutral, left)
        val right_ = simplify(state, ctx.neutral, right)
        eq_(state, ctx, left_, right_)

      case Distinct(exprs) =>
        val exprs_ = exprs.map(simplify(state, ctx.neutral, _))
        distinct(state, ctx, exprs_)

      case Is(arg, fun) =>
        val arg_ = simplify(state, ctx.neutral, arg)
        is(state, ctx, arg_, fun)

      // the annotation does not change the value, hence the polarity is kept
      case As(arg, typ) =>
        val arg_ = simplify(state, ctx, arg)
        As(arg_, typ)

      case Ite(test, left, right) =>
        val test_ = simplify(state, ctx.neutral, test)
        val left_ = simplify(state, ctx.assume(List(test_), Nil), left)
        val right_ = simplify(state, ctx.assume(Nil, List(test_)), right)
        ite(state, ctx, test_, left_, right_)

      case Select(base, index) =>
        val base_ = simplify(state, ctx.neutral, base)
        val index_ = simplify(state, ctx.neutral, index)
        select(state, ctx, base_, index_)

      case Store(base, index, value) =>
        val base_ = simplify(state, ctx.neutral, base)
        val index_ = simplify(state, ctx.neutral, index)
        val value_ = simplify(state, ctx.neutral, value)
        store(state, ctx, base_, index_, value_)

      case Not(phi) =>
        val phi_ = simplify(state, ctx.flip, phi)
        not(state, ctx, phi_)

      case Imp(phi, psi) =>
        // like a disjunction of not phi and psi:
        // the premise is simplified assuming that the conclusion does not hold,
        // and the conclusion is simplified assuming the simplified premise
        val phi_ = simplify(state, ctx.flip.assume(Nil, List(psi)), phi)
        val psi_ = simplify(state, ctx.assume(List(phi_), Nil), psi)
        imp(state, ctx, phi_, psi_)

      case And(phis) =>
        val phis_ = nary(state, ctx, Nil, phis, true)
        and(state, ctx, phis_)

      case Or(phis) =>
        val phis_ = nary(state, ctx, Nil, phis, false)
        or(state, ctx, phis_)

      case UMinus(_) | Plus(_) | Minus(_, _) | Times(_) =>
        arith(state, ctx.neutral, expr)

      case DivBy(left, right) =>
        val left_ = arith(state, ctx.neutral, left)
        val right_ = arith(state, ctx.neutral, right)
        div(state, ctx, left_, right_)

      case Mod(left, right) =>
        val left_ = arith(state, ctx.neutral, left)
        val right_ = arith(state, ctx.neutral, right)
        mod(state, ctx, left_, right_)

      case Lt(left, right) =>
        val left_ = simplify(state, ctx.neutral, left)
        val right_ = simplify(state, ctx.neutral, right)
        lt(state, ctx, left_, right_)

      case Le(left, right) =>
        val left_ = simplify(state, ctx.neutral, left)
        val right_ = simplify(state, ctx.neutral, right)
        le(state, ctx, left_, right_)

      case Gt(left, right) =>
        Lt(right, left)

      case Ge(left, right) =>
        Le(right, left)

      case App(fun, inst, typ, args) =>
        val args_ = args.map(simplify(state, ctx.neutral, _))
        app(state, ctx, fun, inst, typ, args_)

      // bound variables are renamed apart from the context before entering the body
      case Bind(quant, bound, body) =>
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(state, ctx.bind(bound_), re(body))
        bind(state, ctx, quant, bound_, body_)

      case Let(bound, args, body) =>
        val args_ = args.map(simplify(state, ctx.neutral, _))
        val (bound_, re) = ctx.avoid(bound)
        val body_ = simplify(state, ctx.bind(bound_), re(body))
        let(state, ctx, bound_, args_, body_)

  // simplify each of `phis` assuming the others, which hold if `pos` (conjunction)
  // and do not hold otherwise (disjunction);
  // propositions in `done` are already processed (in reverse) and assumed in their simplified form,
  // otherwise e.g. both copies in `a and a` would simplify to true
  def nary(state: State, ctx: Ctx, done: List[Expr], phis: List[Expr], pos: Boolean): List[Expr] =
    phis match
      case Nil =>
        done.reverse

      case phi :: rest =>
        val others = done ++ rest
        val ctx_ =
          if pos
          then ctx.assume(others, Nil)
          else ctx.assume(Nil, others)
        val phi_ = simplify(state, ctx_, phi)
        nary(state, ctx, phi_ :: done, rest, pos)

  // simplify an integer-valued term into the normal form of polynomials
  def arith(state: State, ctx: Ctx, expr: Expr): Expr =
    poly(state, ctx, expr).normalize.toExpr

  // simplify an integer-valued term into a polynomial (not normalized):
  // descend through +, -, * and integer literals, simplify the leaves,
  // which may in turn become arithmetic expressions, and combine the results
  def poly(state: State, ctx: Ctx, expr: Expr): Poly =
    expr match
      case Lit(n: BigInt, Sort.int) =>
        Poly.const(n)

      case UMinus(arg) =>
        val arg_ = poly(state, ctx, arg)
        -arg_

      case Plus(args) =>
        val args_ = args.map(poly(state, ctx, _))
        args_.foldLeft(Poly.zero)(_ + _)

      case Minus(left, right) =>
        val left_ = poly(state, ctx, left)
        val right_ = poly(state, ctx, right)
        left_ - right_

      case Times(args) =>
        val args_ = args.map(poly(state, ctx, _))
        args_.foldLeft(Poly.one)(_ * _)

      case _ =>
        val expr_ = simplify(state, ctx, expr)
        Arith.toPoly(expr_)

  // variables known to be equal to another one are replaced
  def var_(state: State, ctx: Ctx, x: Var): Expr =
    ctx.su.vars.get(x) match
      case Some(y) => y
      case None    => x

  def eq_(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
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
  def distinct(state: State, ctx: Ctx, exprs: List[Expr]): Expr =
    val eqs = for case a :: rest <- exprs.tails.toList; b <- rest yield eq_(state, ctx, a, b)

    if eqs contains True
    then False
    else if eqs forall (_ == False)
    then True
    else
      exprs match
        case List(a, b) => Not(Eq(a, b))
        case _          => Distinct(exprs)

  // testers on constructor applications
  def is(state: State, ctx: Ctx, arg: Expr, fun: Fun): Expr =
    constr(state, arg) match
      case Some(constr) if constr.name == fun.name => True
      case Some(constr)                            => False
      case None                                    => Is(arg, fun)

  // the constructor that `expr` is built by, looking through type annotations
  def constr(state: State, expr: Expr): Option[Fun] =
    expr match
      case As(expr_, _) =>
        constr(state, expr_)

      case App(fun, _, _, _) if state.constrs contains fun.name =>
        Some(fun)

      case _ =>
        None

  def ite(state: State, ctx: Ctx, test: Expr, left: Expr, right: Expr): Expr =
    (test, left, right) match
      case (True, _, _)          => left
      case (False, _, _)         => right
      case _ if left == right    => left
      case (_, True, False)      => test
      case (_, False, True)      => Not(test)
      case _                     => Ite(test, left, right)

  // read over write
  def select(state: State, ctx: Ctx, base: Expr, index: Expr): Expr =
    base match
      case Store(_, index_, value) if index_ == index =>
        value

      case Store(base_, index_, _) if eq_(state, ctx, index_, index) == False =>
        Select(base_, index)

      case _ =>
        Select(base, index)

  def store(state: State, ctx: Ctx, base: Expr, index: Expr, value: Expr): Expr =
    (base, value) match
      // overwritten
      case (Store(base_, index_, _), _) if index_ == index =>
        Store(base_, index, value)

      // writes back what is already stored
      case (_, Select(base_, index_)) if base_ == base && index_ == index =>
        base

      case _ =>
        Store(base, index, value)

  def not(state: State, ctx: Ctx, phi: Expr): Expr =
    phi match
      case True     => False
      case False    => True
      case Not(psi) => psi
      case _        => Not(phi)

  def imp(state: State, ctx: Ctx, phi: Expr, psi: Expr): Expr =
    (phi, psi) match
      case (True, _)          => psi
      case (False, _)         => True
      case (_, True)          => True
      case (_, False)         => Not(phi)
      case _ if phi == psi    => True
      case _                  => Imp(phi, psi)

  // flatten nested conjunctions, drop true and duplicates,
  // false or a complementary pair makes the whole conjunction false
  def and(state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.flatMap(And.flattenStrong).distinct
    if phis_.contains(False) || phis_.exists(phi => phis_ contains Not(phi))
    then False
    else And(phis_)

  // dual to and
  def or(state: State, ctx: Ctx, phis: List[Expr]): Expr =
    val phis_ = phis.flatMap(Or.flattenStrong).distinct
    if phis_.contains(True) || phis_.exists(phi => phis_ contains Not(phi))
    then True
    else Or(phis_)

  // SMT-LIB semantics: for n != 0, m = n * (m div n) + (m mod n) with 0 <= m mod n < |n|,
  // division by zero is unspecified and therefore left alone
  def div(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) if n != 0 =>
        val r = m mod n.abs
        Lit((m - r) / n, Sort.int)

      case (_, Lit(n: BigInt, _)) if n == 1 =>
        left

      // normalized in the next round
      case (_, Lit(n: BigInt, _)) if n == -1 =>
        UMinus(left)

      case _ =>
        DivBy(left, right)

  def mod(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) if n != 0 =>
        Lit(m mod n.abs, Sort.int)

      case (_, Lit(n: BigInt, _)) if n == 1 || n == -1 =>
        Zero

      case _ =>
        Mod(left, right)

  def lt(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case _ if left == right                    => False
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) => if m < n then True else False
      case _                                     => Lt(left, right)

  def le(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    (left, right) match
      case _ if left == right                    => True
      case (Lit(m: BigInt, _), Lit(n: BigInt, _)) => if m <= n then True else False
      case _                                     => Le(left, right)

  // applications of other functions, e.g. user-defined ones
  def app(state: State, ctx: Ctx, fun: Fun, inst: List[Type], typ: Type, args: List[Expr]): Expr =
    App(fun, inst, typ, args)

  // unused bound variables are dropped,
  // the binder vanishes when none remain (sorts are nonempty in SMT-LIB)
  def bind(state: State, ctx: Ctx, quant: Name, bound: List[Var], body: Expr): Expr =
    val bound_ = bound.filter(body.free.contains)
    if bound_.isEmpty
    then body
    else Bind(quant, bound_, body)

  // unused bindings are dropped
  def let(state: State, ctx: Ctx, bound: List[Var], args: List[Expr], body: Expr): Expr =
    val pairs = (bound zip args).filter((x, _) => body.free contains x)
    if pairs.isEmpty
    then body
    else Let(pairs.map(_._1), pairs.map(_._2), body)
