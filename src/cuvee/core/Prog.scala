package cuvee.core

import cuvee.Name
import cuvee.sexpr.Attrs

case class Proc(name: Name, params: List[Param], in: List[Type], out: List[Type])

sealed trait Prog:
  def mod: Set[Var]

case object Break extends Prog:
  def mod = Set()

case object Continue extends Prog:
  def mod = Set()

case object Return extends Prog:
  def mod = Set()

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

case class Call(proc: Name, args: List[Expr], res: List[Var]) extends Prog:
  def mod = Set(res*)

case class Block(locals: List[Var], progs: List[Prog]) extends Prog:
  def mod = progs.mod

case class Choice(progs: List[Prog]) extends Prog:
  def mod = progs.mod

case class If(test: Expr, left: Prog, right: Prog) extends Prog:
  def mod = left.mod ++ right.mod

case class While(test: Expr, body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod