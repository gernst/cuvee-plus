package cuvee.simplify

import util.Name
import cuvee.pipe.Transform
import cuvee.core._

// contextual simplification of the formulas in assertions and function definitions,
// where each subterm is simplified under the facts known to hold at its position
object Simplify extends Transform:
  def apply(prefix: List[Cmd], cmds: List[Cmd], state: State): List[Cmd] =
    for cmd <- cmds
    yield simplify(state, cmd)

  def simplify(state: State, cmd: Cmd): Cmd =
    cmd match
      case Assert(justify, params, phi, attrs) =>
        Assert(justify, params, simplify(state, Ctx.empty, phi), attrs)

      case DefineFun(fun, body, attrs) =>
        DefineFun(fun, simplify(state, Ctx.empty, body), attrs)

      case _ =>
        cmd

  // simplify `expr` assuming that all facts in `ctx` hold
  // by repeated rounds of simplification until a fixpoint is reached
  def simplify(state: State, ctx: Ctx, expr: Expr): Expr =
    val expr_ = once(state, ctx, expr)
    if expr_ == expr
    then expr
    else simplify(state, ctx, expr_)

  // a single round of simplification, dispatching on the builtin functions,
  // subterms are simplified first, where ite and the boolean connectives
  // extend the context by the facts known at the position of each subterm
  def once(state: State, ctx: Ctx, expr: Expr): Expr =
    expr match
      case x: Var =>
        var_(state, ctx, x)

      case _: Lit | True | False =>
        expr

      case Eq(left, right) =>
        val left_ = simplify(state, ctx, left)
        val right_ = simplify(state, ctx, right)
        eq_(state, ctx, left_, right_)

      case Ite(test, left, right) =>
        val test_ = simplify(state, ctx, test)
        val left_ = simplify(state, ctx.assume(List(test_), Nil), left)
        val right_ = simplify(state, ctx.assume(Nil, List(test_)), right)
        ite(state, ctx, test_, left_, right_)

      case Select(base, index) =>
        val base_ = simplify(state, ctx, base)
        val index_ = simplify(state, ctx, index)
        select(state, ctx, base_, index_)

      case Store(base, index, value) =>
        val base_ = simplify(state, ctx, base)
        val index_ = simplify(state, ctx, index)
        val value_ = simplify(state, ctx, value)
        store(state, ctx, base_, index_, value_)

      case Not(phi) =>
        val phi_ = simplify(state, ctx, phi)
        not(state, ctx, phi_)

      case Imp(phi, psi) =>
        // like a disjunction of not phi and psi:
        // the premise is simplified assuming that the conclusion does not hold,
        // and the conclusion is simplified assuming the simplified premise
        val phi_ = simplify(state, ctx.assume(Nil, List(psi)), phi)
        val psi_ = simplify(state, ctx.assume(List(phi_), Nil), psi)
        imp(state, ctx, phi_, psi_)

      case And(phis) =>
        val phis_ = nary(state, ctx, Nil, phis, true)
        and(state, ctx, phis_)

      case Or(phis) =>
        val phis_ = nary(state, ctx, Nil, phis, false)
        or(state, ctx, phis_)

      case UMinus(arg) =>
        val arg_ = simplify(state, ctx, arg)
        uminus(state, ctx, arg_)

      case Plus(args) =>
        val args_ = args.map(simplify(state, ctx, _))
        plus(state, ctx, args_)

      case Minus(left, right) =>
        val left_ = simplify(state, ctx, left)
        val right_ = simplify(state, ctx, right)
        minus(state, ctx, left_, right_)

      case Times(args) =>
        val args_ = args.map(simplify(state, ctx, _))
        times(state, ctx, args_)

      case DivBy(left, right) =>
        val left_ = simplify(state, ctx, left)
        val right_ = simplify(state, ctx, right)
        div(state, ctx, left_, right_)

      case Mod(left, right) =>
        val left_ = simplify(state, ctx, left)
        val right_ = simplify(state, ctx, right)
        mod(state, ctx, left_, right_)

      case Lt(left, right) =>
        val left_ = simplify(state, ctx, left)
        val right_ = simplify(state, ctx, right)
        lt(state, ctx, left_, right_)

      case Le(left, right) =>
        val left_ = simplify(state, ctx, left)
        val right_ = simplify(state, ctx, right)
        le(state, ctx, left_, right_)

      case Gt(left, right) =>
        Lt(right, left)

      case Ge(left, right) =>
        Le(right, left)

      case App(fun, inst, typ, args) =>
        val args_ = args.map(simplify(state, ctx, _))
        app(state, ctx, fun, inst, typ, args_)

      case Bind(quant, bound, body) =>
        val body_ = simplify(state, ctx.bind(bound), body)
        bind(state, ctx, quant, bound, body_)

      case Let(bound, args, body) =>
        val args_ = args.map(simplify(state, ctx, _))
        val body_ = simplify(state, ctx.bind(bound), body)
        let(state, ctx, bound, args_, body_)

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

  def var_(state: State, ctx: Ctx, x: Var): Expr =
    ???

  def eq_(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    ???

  def ite(state: State, ctx: Ctx, test: Expr, left: Expr, right: Expr): Expr =
    ???

  def select(state: State, ctx: Ctx, base: Expr, index: Expr): Expr =
    ???

  def store(state: State, ctx: Ctx, base: Expr, index: Expr, value: Expr): Expr =
    ???

  def not(state: State, ctx: Ctx, phi: Expr): Expr =
    ???

  def imp(state: State, ctx: Ctx, phi: Expr, psi: Expr): Expr =
    ???

  def and(state: State, ctx: Ctx, phis: List[Expr]): Expr =
    ???

  def or(state: State, ctx: Ctx, phis: List[Expr]): Expr =
    ???

  def uminus(state: State, ctx: Ctx, arg: Expr): Expr =
    ???

  def plus(state: State, ctx: Ctx, args: List[Expr]): Expr =
    ???

  def minus(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    ???

  def times(state: State, ctx: Ctx, args: List[Expr]): Expr =
    ???

  def div(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    ???

  def mod(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    ???

  def lt(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    ???

  def le(state: State, ctx: Ctx, left: Expr, right: Expr): Expr =
    ???

  // applications of other functions, e.g. user-defined ones
  def app(state: State, ctx: Ctx, fun: Fun, inst: List[Type], typ: Type, args: List[Expr]): Expr =
    ???

  def bind(state: State, ctx: Ctx, quant: Name, bound: List[Var], body: Expr): Expr =
    ???

  def let(state: State, ctx: Ctx, bound: List[Var], args: List[Expr], body: Expr): Expr =
    ???
