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
    expr match
      case _: Var | _: Lit =>
        expr

      case Old(arg) =>
        val arg_ = elim(gs, gs_, arg)
        Subst.from(gs, gs_)(arg_)

      case App(fun, inst, typ, args) =>
        val args_ = elim(gs, gs_, args)
        App(fun, inst, typ, args_)

      case Distinct(exprs) =>
        val exprs_ = elim(gs, gs_, exprs)
        Distinct(exprs_)

      case Is(arg, fun) =>
        val arg_ = elim(gs, gs_, arg)
        Is(arg_, fun)

      case As(arg, typ) =>
        val arg_ = elim(gs, gs_, arg)
        As(arg_, typ)

      case Diff(xs, arg) =>
        val arg_ = elim(gs, gs_, arg)
        Diff(xs, arg_)

      case Trace(init, deps, acc, bound, update) =>
        val init_ = elim(gs, gs_, init)
        val deps_ = elim(gs, gs_, deps)
        val update_ = for (guard, result) <- update yield (elim(gs, gs_, guard), elim(gs, gs_, result))
        Trace(init_, deps_, acc, bound, update_)

      case Maps(deps, bound, update) =>
        val deps_ = elim(gs, gs_, deps)
        val update_ = for (guard, result) <- update yield (elim(gs, gs_, guard), elim(gs, gs_, result))
        Maps(deps_, bound, update_)

      case Invs(deps, bound, body) =>
        val deps_ = elim(gs, gs_, deps)
        val body_ = elim(gs, gs_, body)
        Invs(deps_, bound, body_)

      case Bind(quant, bound, body) =>
        val body_ = elim(gs, gs_, body)
        Bind(quant, bound, body_)

      case Let(bound, args, body) =>
        val args_ = elim(gs, gs_, args)
        val body_ = elim(gs, gs_, body)
        Let(bound, args_, body_)

  @targetName("elimExprs")
  def elim(gs: List[Var], gs_ : List[Expr], exprs: List[Expr]): List[Expr] =
    for expr <- exprs
    yield elim(gs, gs_, expr)

  def elim(gs: List[Var], gs_ : List[Expr], attrs: Attrs): Attrs =
    val attrs_ =
      for (kw, arg) <- attrs.attrs
      yield arg match
        case Some(expr: Expr) => (kw, Some(elim(gs, gs_, expr)))
        case _                => (kw, arg)

    Attrs(attrs_)

  // in all expressions and attributes of a program, e.g. assertions and loop invariants
  def elim(gs: List[Var], gs_ : List[Expr], prog: Prog): Prog =
    prog match
      case Break | Continue | Return =>
        prog

      case Spec(xs, pre, post) =>
        val pre_ = elim(gs, gs_, pre)
        val post_ = elim(gs, gs_, post)
        Spec(xs, pre_, post_)

      case Assign(xs, rhs) =>
        val rhs_ = elim(gs, gs_, rhs)
        Assign(xs, rhs_)

      case Call(proc, args, res) =>
        val args_ = elim(gs, gs_, args)
        Call(proc, args_, res)

      case Block(locals, progs) =>
        val progs_ = progs.map(elim(gs, gs_, _))
        Block(locals, progs_)

      case Choice(progs) =>
        val progs_ = progs.map(elim(gs, gs_, _))
        Choice(progs_)

      case If(test, left, right) =>
        val test_ = elim(gs, gs_, test)
        val left_ = elim(gs, gs_, left)
        val right_ = elim(gs, gs_, right)
        If(test_, left_, right_)

      case While(test, body, attrs) =>
        val test_ = elim(gs, gs_, test)
        val body_ = elim(gs, gs_, body)
        val attrs_ = elim(gs, gs_, attrs)
        While(test_, body_, attrs_)

      case Iter(body, attrs) =>
        val body_ = elim(gs, gs_, body)
        val attrs_ = elim(gs, gs_, attrs)
        Iter(body_, attrs_)

      case Ode(xs, rhs, dom, attrs) =>
        val rhs_ = elim(gs, gs_, rhs)
        val dom_ = elim(gs, gs_, dom)
        val attrs_ = elim(gs, gs_, attrs)
        Ode(xs, rhs_, dom_, attrs_)

      case Par(calls) =>
        val calls_ =
          for Call(proc, args, res) <- calls
          yield Call(proc, elim(gs, gs_, args), res)
        Par(calls_)

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
case class Maps(deps: List[Expr], bound: List[Var], update: List[(Expr, Expr)]) extends Expr:
  def subexprs = deps ++ Update.exprs(update)
  def params = deps.params ++ bound.params ++ Update.params(update)
  def free = deps.free ++ (Update.free(update) -- bound)

  def typ =
    Error.report("map without update", this):
      require(update.nonEmpty)
    Sort.seq(update.head._2.typ)

// all(for deps check bound ↦ body): the condition holds for all values of the dependencies, point-wise
case class Invs(deps: List[Expr], bound: List[Var], body: Expr) extends Expr:
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
