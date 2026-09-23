package cuvee.core

import cuvee.Name

case class Proc(name: Name, params: List[Param], in: List[Type], out: List[Type])

sealed trait Prog:
  def mod: Set[Var]

case class Spec(xs: List[Var], pre: Expr, post: Expr) extends Prog:
  def mod = Set(xs*)

object Spec:
  def havoc(xs: List[Var]) =
    Spec(xs, True, True)

  def assume(pre: Expr) =
    Spec(Nil, pre, True)

  def assert(post: Expr) =
    Spec(Nil, True, post)

case class Assign(lhs: List[Var], rhs: List[Expr]) extends Prog:
  def mod = Set(lhs*)

case class Block(progs: List[Prog]) extends Prog:
  def mod = progs.mod

case class Choice(progs: List[Prog]) extends Prog:
  def mod = progs.mod
