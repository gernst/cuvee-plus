package cuvee.core

import scala.annotation.targetName

import cuvee.Name

case class Scope(params: Map[Name, Param], bound: Map[Name, Var]):
  @targetName("Scope.addParam")
  def ++(that: List[Param]) =
    Scope(params ++ that.asIndex, bound)

  @targetName("Scope.addVars")
  def ++(that: List[Var]) =
    Scope(params, bound ++ that.asIndex)

object Scope:
  val empty = Scope(Map(), Map())

  def apply(params: List[Param], formals: List[Var] = Nil): Scope =
    Scope(Map(params.asIndex*), Map(formals.asIndex*))
