package cuvee.pure

import cuvee.Name

case class Con(name: Name, arity: Int)
case class Data(params: List[Param], constrs: List[(Fun, List[Fun])])

sealed trait Type
case class Param(name: Name) extends Type
case class Sort(con: Con, args: List[Type]) extends Type

object Con:
  val bool = Con("Bool", 0)
  val int = Con("Int", 0)
  val real = Con("Real", 0)

object Sort:
  val bool = Sort(Con.bool, Nil)
  val int = Sort(Con.int, Nil)
  val real = Sort(Con.real, Nil)
