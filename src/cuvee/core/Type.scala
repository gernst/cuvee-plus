package cuvee.core

import cuvee.Name

case class Con(name: Name, arity: Int)
case class Data(params: List[Param], constrs: List[(Fun, List[Fun])])

sealed trait Type:
  def params: Set[Param]

case class Param(name: Name) extends Type:
  def params = Set(this)

  def asIndex = (name, this)

case class Sort(con: Con, args: List[Type]) extends Type:
  def params = args.params

object Param:
  val a = Param("a")
  val b = Param("b")

object Con:
  val bool = Con("Bool", 0)
  val int = Con("Int", 0)
  val real = Con("Real", 0)
  val string = Con("String", 0)
  val array = Con("Array", 2)

object Sort:
  val bool = Sort(Con.bool, Nil)
  val int = Sort(Con.int, Nil)
  val real = Sort(Con.real, Nil)
  val string = Sort(Con.string, Nil)

object Type:
  def check(scope: Scope, expr: Expr, typ: Type): Expr =
    ???
