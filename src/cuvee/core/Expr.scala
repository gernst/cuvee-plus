package cuvee.core

import scala.annotation.targetName

import cuvee.Name
import cuvee.util.Counter

case class LetEq(x: Var, rhs: Expr):
  def params = x.params ++ rhs.params
  def bound = Set(x)
  def free = rhs.free

sealed trait Expr:
  def params: Set[Param]
  def free: Set[Var]

object Expr:
  def vars(name: String, types: List[Type]) =
    for (typ, index) <- types.zipWithIndex
    yield Var(Name(name, Some(index)), typ)

case class Var(name: Name, typ: Type) extends Expr with Counter:
  def params = typ.params
  def free = Set(this)

  def asPair = (name, typ)
  def asIndex = (name, this)

  def fresh = Var(name.withIndex(next()), typ)

case class Lit(value: Any, typ: Type) extends Expr:
  def params = typ.params
  def free = Set()

case class App(fun: Fun, inst: List[Type], args: List[Expr]) extends Expr:
  def params = inst.params ++ args.params
  def free = args.free

case class Bind(quant: Name, bound: List[Var], body: Expr) extends Expr:
  def params = bound.params ++ body.params
  def free = body.free -- bound

case class Let(eqs: List[LetEq], body: Expr) extends Expr:
  def params = eqs.params
  def free = eqs.free ++ (body.free -- eqs.bound)
