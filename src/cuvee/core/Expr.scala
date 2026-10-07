package cuvee.core

import scala.annotation.targetName

import util.Name
import util.Counter
import cuvee.Error

sealed trait Expr:
  def params: Set[Param]
  def free: Set[Var]
  def typ: Type

  // apply `f` to the immediate subexpressions point-wise,
  // the bound variables of binders and combinators are kept, i.e., `f` must avoid capture itself
  // the subexpressions are visited from left to right, such that `f` may be used for its side effects only
  def map(f: Expr => Expr): Expr =
    this match
      case _: Var | _: Lit                      => this
      case App(fun, inst, typ, args)            => App(fun, inst, typ, args.map(f))
      case Distinct(exprs)                      => Distinct(exprs.map(f))
      case Is(arg, fun)                         => Is(f(arg), fun)
      case As(arg, typ)                         => As(f(arg), typ)
      case Diff(xs, arg)                        => Diff(xs, f(arg))
      case Old(arg)                             => Old(f(arg))
      case Trace(init, deps, acc, bound, upds)  => Trace(f(init), deps.map(f), acc, bound, upds.map(f))
      case Maps(deps, bound, upds)              => Maps(deps.map(f), bound, upds.map(f))
      case Invs(deps, bound, body)              => Invs(deps.map(f), bound, f(body))
      case Bind(quant, bound, body)             => Bind(quant, bound, f(body))
      case Let(bound, args, body)               => Let(bound, args.map(f), f(body))
      case Match(arg, cases)                    => Match(f(arg), cases.map(f))

  // the expression without type annotations e as T
  def removeAs: Expr =
    this match
      case As(arg, _) => arg.removeAs
      case _          => map(_.removeAs)

object Expr:
  // TODO: structural ordering, for now by the printed representation
  given Ordering[Expr] = Ordering.by(_.toString)

  def vars(name: String, types: List[Type]) =
    for (typ, index) <- types.zipWithIndex
    yield Var(Name(name, Some(index)), typ)

case class Var(name: Name, typ: Type) extends Expr:
  def params = typ.params
  def free = Set(this)

  def asPair = (name, typ)
  def asIndex = (name, this)

  def fresh = 
    Var(name.withIndex(Var.next()), typ)

  // the variable for the derivative of this one, x'
  def primed =
    Var(name.primed, typ)

object Var extends Counter

case class Lit(value: Any, typ: Type) extends Expr:
  def params = typ.params
  def free = Set()

object App:
  // instantiate the type parameters of `fun` by matching its argument types against those of `args`,
  // where the defined sorts of `state` are unfolded, and expanded in the result (see Type.expand)
  def apply(state: State, fun: Fun, args: List[Expr]): App =
    val inst = args.types
    val su = Type.bind(state, fun.args, inst)
    val typ = Type.expand(state, su(fun.res))
    App(fun, inst, typ, args)

  // the same without defined sorts, where there is no state (e.g. sugar)
  def apply(fun: Fun, args: List[Expr]): App =
    App(State.empty, fun, args)

case class App(fun: Fun, inst: List[Type], typ: Type, args: List[Expr]) extends Expr:
  def params = inst.params ++ args.params
  def free = args.free

// pairwise distinctness of two or more expressions of the same type, n-ary as in SMT-LIB
case class Distinct(exprs: List[Expr]) extends Expr:
  def params = exprs.params
  def free = exprs.free
  def typ = Sort.bool

// whether `expr` is built by the constructor `fun` of a datatype
case class Is(expr: Expr, fun: Fun) extends Expr:
  def params = expr.params
  def free = expr.free
  def typ = Sort.bool

// explicit type annotation, e.g. for polymorphic constants
case class As(expr: Expr, typ: Type) extends Expr:
  def params = expr.params ++ typ.params
  def free = expr.free

// the (time-)derivative of `expr` with respect to the variables `xs`, i.e., the sum of ∂expr/∂x * x' for x in xs,
// where the variables xs are ordinary free variables without primes, which are introduced only by computing
// the derivative (see Simplify.diff); xs must be on Real;
// the primed variables are free, too, since the derivative refers to them once it is computed
case class Diff(xs: List[Var], expr: Expr) extends Expr:
  def params = xs.params ++ expr.params
  def free = expr.free ++ xs ++ xs.primed
  def typ = expr.typ

// the value of `expr` at the entry of the enclosing procedure, where the global variables have their initial values,
// eliminated by `Old.elim` before verification
case class Old(expr: Expr) extends Expr:
  def params = expr.params
  def free = expr.free
  def typ = expr.typ

object Old:
  // replace old(e) by e[gs := gs_], where gs_ are the values of the global variables gs at the entry,
  // nested occurrences of old refer to the same values
  def elim(gs: List[Var], gs_ : List[Expr], expr: Expr): Expr =
    instance(Subst.empty, Subst.from(gs, gs_), expr)

  // a single traversal that replaces the free variables by `now`, and inside of old(e) by `before`, and strips old,
  // e.g. for the postcondition of a call, whose modified global variables refer to their new values outside of old
  // and to their values before the call inside of it (see Verify.instance); `Subst` substitutes inside old(e) as well;
  // the type parameters are instantiated by `now`
  def instance(now: Subst[Type, Expr], before: Subst[Type, Expr], expr: Expr): Expr =
    instance(now, before, false, expr)

  // `old` holds inside of old(e)
  def instance(now: Subst[Type, Expr], before: Subst[Type, Expr], old: Boolean, expr: Expr): Expr =
    val su = if old then before else now

    // the variables bound in the context are no longer replaced, those that would capture
    // a free variable of the replacements are renamed, also in the patterns of cases
    def bind(xs: List[Var]): (List[Var], Expr => Expr) =
      val (rename, now_) = now.avoid(xs, now.free ++ before.free)
      val before_ = Subst(before.params, before.vars -- xs ++ rename.vars)
      (rename.lhs(xs), instance(now_, before_, old, _))

    expr match
      case x: Var                    => su(x)
      case Lit(value, typ)           => Lit(value, now(typ))
      case App(fun, inst, typ, args) => App(fun, now(inst), now(typ), args.map(instance(now, before, old, _)))
      case As(arg, typ)              => As(instance(now, before, old, arg), now(typ))
      case Diff(xs, arg)             => Diff(su.lhs(xs), instance(now, before, old, arg))
      case Old(arg)                  => instance(now, before, true, arg)

      case Bind(quant, bound, body) =>
        val (bound_, inner) = bind(bound)
        Bind(quant, bound_, inner(body))

      case Trace(init, deps, acc, bound, updates) =>
        val (acc_ :: bound_, inner) = bind(acc :: bound): @unchecked
        Trace(instance(now, before, old, init), deps.map(instance(now, before, old, _)), acc_, bound_, updates.map(inner))

      case Maps(deps, bound, updates) =>
        val (bound_, inner) = bind(bound)
        Maps(deps.map(instance(now, before, old, _)), bound_, updates.map(inner))

      case Invs(deps, bound, body) =>
        val (bound_, inner) = bind(bound)
        Invs(deps.map(instance(now, before, old, _)), bound_, inner(body))

      case Let(bound, args, body) =>
        val (bound_, inner) = bind(bound)
        Let(bound_, args.map(instance(now, before, old, _)), inner(body))

      case Match(arg, cases) =>
        val cases_ =
          for Case(pat, body, cond) <- cases
          yield
            val (_, inner) = bind(pat.free.toList)
            Case(inner(pat), inner(body), inner(cond))
        Match(instance(now, before, old, arg), cases_)

      case _ =>
        expr.map(instance(now, before, old, _))

  // in all expressions and attributes of a program, e.g. assertions and loop invariants
  def elim(gs: List[Var], gs_ : List[Expr], prog: Prog): Prog =
    prog.map(elim(gs, gs_, _: Expr), elim(gs, gs_, _: Prog))

// the combinators of trace equation systems, which describe the computation of a loop per variable;
// their dependencies `deps` are sequences of the same length, over which the variables `bound` range point-wise,
// and their updates are guarded results, if φ₁ then e₁, ..., if φₚ then eₚ, with disjoint and complete guards,
// each case of which is an Upd(φᵢ, eᵢ)
case class Upd(cond: Expr, rhs: Expr):
  def params = cond.params ++ rhs.params
  def free = cond.free ++ rhs.free

  def map(f: Expr => Expr) =
    Upd(f(cond), f(rhs))

// trace(init, for deps do acc, bound ↦ update): the trace of the values of the accumulator `acc`,
// starting from `init`, where each subsequent value is computed by the update from the previous one
// and the corresponding values of the dependencies, one entry longer than the dependencies
case class Trace(init: Expr, deps: List[Expr], acc: Var, bound: List[Var], updates: List[Upd]) extends Expr:
  def params = init.params ++ deps.params ++ (acc :: bound).params ++ updates.params
  def free = init.free ++ deps.free ++ (updates.free -- (acc :: bound))
  def typ = Sort.trace(acc.typ)

// map(for deps yield bound ↦ update): the sequence of the results of the update for the values of the dependencies,
// point-wise, which has the same length as the dependencies
case class Maps(deps: List[Expr], bound: List[Var], updates: List[Upd]) extends Expr:
  def params = deps.params ++ bound.params ++ updates.params
  def free = deps.free ++ (updates.free -- bound)

  // there is at least one case, see Type.check
  def typ = Sort.seq(updates.head.rhs.typ)

// all(for deps check bound ↦ body): the condition holds for all values of the dependencies, point-wise
case class Invs(deps: List[Expr], bound: List[Var], body: Expr) extends Expr:
  def params = deps.params ++ bound.params ++ body.params
  def free = deps.free ++ (body.free -- bound)
  def typ = Sort.bool

case class Bind(quant: Name, bound: List[Var], body: Expr) extends Expr:
  def params = bound.params ++ body.params
  def free = body.free -- bound
  def typ = body.typ

case class Let(bound: List[Var], args: List[Expr], body: Expr) extends Expr:
  def params = bound.params ++ args.params ++ body.params
  def free = args.free ++ (body.free -- bound)
  def typ = body.typ

// a case of a match expression, which applies if the argument matches the pattern and the condition holds,
// the pattern consists of variables and constructor applications (see Type.check), whose variables are bound
// in the body and the condition; conditions are not part of SMT-LIB, where they are always true
case class Case(pat: Expr, body: Expr, cond: Expr):
  def bound = pat.free
  def params = pat.params ++ body.params ++ cond.params
  def free = body.free ++ cond.free -- bound

  // the pattern is kept, like the bound variables of binders
  def map(f: Expr => Expr) =
    Case(pat, f(body), f(cond))

// the result of the first case whose pattern matches `arg` and whose condition holds
case class Match(arg: Expr, cases: List[Case]) extends Expr:
  def params = arg.params ++ cases.params
  def free = arg.free ++ cases.free

  // there is at least one case, see Type.check
  def typ = cases.head.body.typ
