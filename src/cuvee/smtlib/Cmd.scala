package cuvee.smtlib

import cuvee.Name
import cuvee.pure._
import cuvee.prog._
import cuvee.sexpr.Attrs

trait Result

enum Ack extends Result:
  case Success
  case Unsupported

enum Status extends Result:
  case Unknown
  case Sat
  case Unsat

case class Error(msg: String) extends Throwable with Result

case class Labels(labels: List[String]) extends Result

sealed trait Cmd
sealed trait Ctrl extends Cmd
sealed trait Decl extends Cmd
sealed trait Query extends Cmd

case object CheckSat extends Query
case object Labels extends Query
case object GetModel extends Query

case object Exit extends Throwable with Ctrl
case object Push extends Ctrl
case object Pop extends Ctrl
case object Reset extends Ctrl

case class SetLogic(name: String) extends Decl

case class GetOption(name: String) extends Decl
case class SetOption(name: String, value: Any) extends Decl

case class GetInfo(name: String) extends Decl
case class SetInfo(name: String, value: Any) extends Decl

case class DeclareSort(con: Con) extends Decl
case class DeclareFun(fun: Fun) extends Decl
case class DeclareProc(proc: Proc) extends Decl

enum Justify:
  case Axiom
  case Goal
  case Lemma
  // case Free // should be done as an attribute

case class Assert(params: List[Param], phi: Expr, attrs: Attrs, justify: Justify) extends Decl
