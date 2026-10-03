package cuvee.core

import scala.annotation.targetName

import util.Name

case class Scope(params: Map[Name, Param], vars: Map[Name, Var]):
  @targetName("Scope.addParam")
  def ++(that: List[Param]) =
    Scope(params ++ that.asIndex, vars)

  @targetName("Scope.addVars")
  def ++(that: List[Var]) =
    Scope(params, vars ++ that.asIndex)

object Scope:
  val empty = Scope(Map(), Map())

  def apply(params: List[Param], formals: List[Var] = Nil): Scope =
    Scope(Map(params.asIndex*), Map(formals.asIndex*))
