package cuvee.core

import scala.annotation.targetName

import util.Name
import util.Counter
import cuvee.Error

sealed trait Expr:
  def params: Set[Param]
  def free: Set[Var]
  def typ: Type
  // the immediate subexpressions
  def subexprs: List[Expr]

object Expr:
  // TODO: structural ordering, for now by the printed representation
  given Ordering[Expr] = Ordering.by(_.toString)

  def vars(name: String, types: List[Type]) =
    for (typ, index) <- types.zipWithIndex
    yield Var(Name(name, Some(index)), typ)

case class Var(name: Name, typ: Type) extends Expr:
  def subexprs = Nil
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
  def subexprs = Nil
  def params = typ.params
  def free = Set()

object App:
  // instantiate the type parameters of `fun` by matching its argument types against those of `args`
  def apply(fun: Fun, args: List[Expr]): App =
    val inst = args.types
    val su = Type.bind(fun.args, inst)
    val typ = su(fun.res)
    App(fun, inst, typ, args)

case class App(fun: Fun, inst: List[Type], typ: Type, args: List[Expr]) extends Expr:
  def subexprs = args
  def params = inst.params ++ args.params
  def free = args.free
  // def typ = ???

// pairwise distinctness of two or more expressions of the same type, n-ary as in SMT-LIB
case class Distinct(exprs: List[Expr]) extends Expr:
  def subexprs = exprs
  def params = exprs.params
  def free = exprs.free
  def typ = Sort.bool

// whether `expr` is built by the constructor `fun` of a datatype
case class Is(expr: Expr, fun: Fun) extends Expr:
  def subexprs = List(expr)
  def params = expr.params
  def free = expr.free
  def typ = Sort.bool

// explicit type annotation, e.g. for polymorphic constants
case class As(expr: Expr, typ: Type) extends Expr:
  def subexprs = List(expr)
  def params = expr.params ++ typ.params
  def free = expr.free

// the (time-)derivative of `expr` with respect to the variables `xs`, i.e., the sum of ∂expr/∂x * x' for x in xs,
// where the variables xs are ordinary free variables without primes, which are introduced only by computing
// the derivative (see Simplify.diff); xs must be on Real
case class Diff(xs: List[Var], expr: Expr) extends Expr:
  def subexprs = List(expr)
  def params = xs.params ++ expr.params
  def free = expr.free ++ xs
  def typ = expr.typ

// the value of `expr` at the entry of the enclosing procedure, where the global variables have their initial values,
// eliminated by `Old.elim` before verification
case class Old(expr: Expr) extends Expr:
  def subexprs = List(expr)
  def params = expr.params
  def free = expr.free
  def typ = expr.typ

object Old:
  // replace old(e) by e[gs := gs_], where gs_ are the values of the global variables gs at the entry,
  // nested occurrences of old refer to the same values
  def elim(gs: List[Var], gs_ : List[Expr], expr: Expr): Expr =
    val su = Subst.from(gs, gs_)
    val e = (expr: Expr) => elim(gs, gs_, expr)
    expr match
      case _: Var | _: Lit         => expr
      case Old(arg)                => su(e(arg))
      case App(fun, inst, typ, args) => App(fun, inst, typ, args.map(e))
      case Distinct(exprs)         => Distinct(exprs.map(e))
      case Is(arg, fun)            => Is(e(arg), fun)
      case As(arg, typ)            => As(e(arg), typ)
      case Diff(xs, arg)           => Diff(xs, e(arg))
      case Bind(quant, bound, body) => Bind(quant, bound, e(body))
      case Let(bound, args, body)  => Let(bound, args.map(e), e(body))

  def elim(gs: List[Var], gs_ : List[Expr], attrs: cuvee.core.Attrs): cuvee.core.Attrs =
    val attrs_ =
      for (kw, arg) <- attrs.attrs
      yield arg match
        case Some(expr: Expr) => (kw, Some(elim(gs, gs_, expr)))
        case _                => (kw, arg)

    cuvee.core.Attrs(attrs_)

  // in all expressions and attributes of a program, e.g. assertions and loop invariants
  def elim(gs: List[Var], gs_ : List[Expr], prog: Prog): Prog =
    val e = (expr: Expr) => elim(gs, gs_, expr)
    val p = (prog: Prog) => elim(gs, gs_, prog)
    val a = (attrs: cuvee.core.Attrs) => elim(gs, gs_, attrs)
    prog match
      case Break | Continue | Return  => prog
      case Spec(xs, pre, post)        => Spec(xs, e(pre), e(post))
      case Assign(xs, rhs)            => Assign(xs, rhs.map(e))
      case Call(proc, args, res)      => Call(proc, args.map(e), res)
      case Block(locals, progs)       => Block(locals, progs.map(p))
      case Choice(progs)              => Choice(progs.map(p))
      case If(test, left, right)      => If(e(test), p(left), p(right))
      case While(test, body, attrs)   => While(e(test), p(body), a(attrs))
      case Iter(body, attrs)          => Iter(p(body), a(attrs))
      case Ode(xs, rhs, dom, attrs)   => Ode(xs, rhs.map(e), e(dom), a(attrs))
      case Par(calls)                 => Par(for Call(proc, args, res) <- calls yield Call(proc, args.map(e), res))

// the combinators of trace equation systems, which describe the computation of a loop per variable;
// their dependencies `deps` are sequences of the same length, over which the variables `bound` range point-wise,
// and their updates are guarded results, if φ₁ then e₁, ..., if φₚ then eₚ, with disjoint and complete guards
object Update:
  def free(update: List[(Expr, Expr)]): Set[Var] =
    update.flatMap((guard, result) => guard.free ++ result.free).toSet

  def params(update: List[(Expr, Expr)]): Set[Param] =
    update.flatMap((guard, result) => guard.params ++ result.params).toSet

  def exprs(update: List[(Expr, Expr)]): List[Expr] =
    update.flatMap((guard, result) => List(guard, result))

// trace(init, for deps do acc, bound ↦ update): the trace of the values of the accumulator `acc`,
// starting from `init`, where each subsequent value is computed by the update from the previous one
// and the corresponding values of the dependencies, one entry longer than the dependencies
case class Trace(init: Expr, deps: List[Expr], acc: Var, bound: List[Var], update: List[(Expr, Expr)]) extends Expr:
  def subexprs = init :: deps ++ Update.exprs(update)
  def params = init.params ++ deps.params ++ (acc :: bound).params ++ Update.params(update)
  def free = init.free ++ deps.free ++ (Update.free(update) -- (acc :: bound))
  def typ = Sort.trace(acc.typ)

// map(for deps yield bound ↦ update): the sequence of the results of the update for the values of the dependencies,
// point-wise, which has the same length as the dependencies
case class TraceMap(deps: List[Expr], bound: List[Var], update: List[(Expr, Expr)]) extends Expr:
  def subexprs = deps ++ Update.exprs(update)
  def params = deps.params ++ bound.params ++ Update.params(update)
  def free = deps.free ++ (Update.free(update) -- bound)

  def typ =
    Error.report("map without update", this):
      require(update.nonEmpty)
    Sort.seq(update.head._2.typ)

// all(for deps check bound ↦ body): the condition holds for all values of the dependencies, point-wise
case class TraceAll(deps: List[Expr], bound: List[Var], body: Expr) extends Expr:
  def subexprs = deps :+ body
  def params = deps.params ++ bound.params ++ body.params
  def free = deps.free ++ (body.free -- bound)
  def typ = Sort.bool

case class Bind(quant: Name, bound: List[Var], body: Expr) extends Expr:
  def subexprs = List(body)
  def params = bound.params ++ body.params
  def free = body.free -- bound
  def typ = body.typ

case class Let(bound: List[Var], args: List[Expr], body: Expr) extends Expr:
  def subexprs = args :+ body
  def params = bound.params ++ args.params ++ body.params
  def free = args.free ++ (body.free -- bound)
  def typ = body.typ
