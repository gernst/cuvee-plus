package cuvee.core

import cuvee.Name
import cuvee.core._
import cuvee.sexpr.Attrs

trait Result

enum Ack extends Result:
  case Success
  case Unsupported

enum Status extends Result:
  case Unknown
  case Sat
  case Unsat

case class Labels(labels: List[String]) extends Result

sealed trait Cmd

sealed trait Ctrl extends Cmd
sealed trait Decl extends Cmd
sealed trait Query extends Cmd

case object CheckSat extends Query
case object Labels extends Query
case object GetModel extends Query

case object Exit extends Throwable with Ctrl:
  override def toString =
    "Exit"

case object Push extends Ctrl
case object Pop extends Ctrl
case object Reset extends Ctrl

case class SetLogic(name: String) extends Decl

case class GetOption(name: String) extends Query
case class SetOption(name: String, value: Any) extends Decl

case class GetInfo(name: String) extends Query
case class SetInfo(name: String, value: Any) extends Decl

case class DeclareSort(con: Con, attrs: Attrs) extends Decl
case class DefineSort(con: Con, params: List[Param], body: Type, attrs: Attrs) extends Decl

case class DeclareFun(fun: Fun, attrs: Attrs) extends Decl
case class DefineFun(fun: Fun, formals: List[Var], body: Expr, attrs: Attrs) extends Decl

case class DeclareProc(proc: Proc, attrs: Attrs) extends Decl
case class DefineProc(proc: Proc, in: List[Var], out: List[Var], body: Prog, attrs: Attrs) extends Decl

sealed trait Justify
case object Axiom extends Justify
case object Goal extends Justify
case object Lemma extends Justify

case class Assert(justify: Justify, params: List[Param], phi: Expr, attrs: Attrs) extends Decl
