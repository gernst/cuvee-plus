package cuvee.core

import cuvee.Name

case class Proc(name: Name, params: List[Param], in: List[Type], out: List[Type])

case class Body(spec: Spec, body: Prog)

sealed trait Prog

case class Spec(mod: List[Name], pre: Expr, post: Expr) extends Prog
case class Assign(lhs: List[Var], rhs: List[Expr]) extends Prog
case class Block(progs: List[Prog]) extends Prog
case class Choice(progs: List[Prog]) extends Prog
