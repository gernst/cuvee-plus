package cuvee.core

import util.Name
import cuvee.sexpr.Attrs

case class Proc(name: Name, params: List[Param], in: List[Var], out: List[Var]):
  def args = in.types
  def res = out.types

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

  def assume(phi: Expr) =
    Spec(Nil, True, phi)

  def assert(phi: Expr) =
    Spec(Nil, phi, True)

case class Assign(lhs: List[Var], rhs: List[Expr]) extends Prog:
  def mod = Set(lhs*)

case class Call(proc: Name, args: List[Expr], res: List[Var]) extends Prog:
  def mod = Set(res*)

case class Block(locals: List[Var], progs: List[Prog]) extends Prog:
  def mod = progs.mod -- locals

case class Choice(progs: List[Prog]) extends Prog:
  def mod = progs.mod

case class If(test: Expr, left: Prog, right: Prog) extends Prog:
  def mod = left.mod ++ right.mod

case class While(test: Expr, body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod

// a loop with a nondeterministic number of iterations, while * { body },
// which corresponds to the repetition of hybrid programs in dL
case class Iter(body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod
