package cuvee.prog

import cuvee.Name
import cuvee.pure._

case class Proc(name: Name, params: List[Param], in: List[Var], out: List[Var])

case class Body(spec: Spec, body: Prog)

sealed trait Prog

case class Spec(mod: List[Name], pre: Expr, post: Expr) extends Prog
case class Assign(eqs: List[LetEq]) extends Prog
case class Block(progs: List[Prog]) extends Prog
case class Choice(progs: List[Prog]) extends Prog
