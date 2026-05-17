package cuvee.smtlib

import cuvee.Name
import cuvee.pure._
import cuvee.prog._

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
sealed trait Decl extends Cmd

case object Exit extends Throwable with Cmd

case object CheckSat extends Cmd
case object Labels extends Cmd
case object GetModel extends Cmd

case object Push extends Cmd
case object Pop extends Cmd
case object Reset extends Cmd

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
  case Free
  case Goal
  case Lemma

case class Assert(phi: Expr, justify: Justify) extends Decl
