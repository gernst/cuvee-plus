package cuvee.core

import scala.annotation.targetName

import util.Name
import util.Counter

sealed trait Expr:
  def params: Set[Param]
  def free: Set[Var]
  def typ: Type

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

object Var extends Counter

case class Lit(value: Any, typ: Type) extends Expr:
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
  def params = inst.params ++ args.params
  def free = args.free
  // def typ = ???

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

case class Bind(quant: Name, bound: List[Var], body: Expr) extends Expr:
  def params = bound.params ++ body.params
  def free = body.free -- bound
  def typ = body.typ

case class Let(bound: List[Var], args: List[Expr], body: Expr) extends Expr:
  def params = bound.params ++ args.params ++ body.params
  def free = args.free ++ (body.free -- bound)
  def typ = body.typ
