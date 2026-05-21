package cuvee.core

import cuvee.Name

case class Scope(params: Set[Param], bound: Map[Name, Type])

object Scope:
  val empty = Scope(Set(), Map())

case class LetEq(name: Name, rhs: Expr)

case class Fun(name: Name, params: List[Param], args: List[Type], res: Type)

sealed trait Expr

case class Var(name: Name, typ: Type) extends Expr
case class Lit(value: Any, typ: Type) extends Expr
case class App(fun: Fun, inst: List[Type], args: List[Expr]) extends Expr
case class Bind(quant: Name, bound: List[Var], body: Expr) extends Expr
case class Let(eqs: List[LetEq], body: Expr) extends Expr
