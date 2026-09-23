package cuvee.core

import cuvee.Name
import scala.annotation.targetName

case class Fun(name: Name, params: List[Param], args: List[Type], res: Type):
  def arity = args.length

object Fun:
  val true_ = Fun("true", Nil, Nil, Sort.bool)
  val false_ = Fun("false", Nil, Nil, Sort.bool)
