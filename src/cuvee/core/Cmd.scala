package cuvee.core

import util.Name
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

// answer to get-info, a list of keywords with values
case class Info(attrs: Attrs) extends Result

// answer to get-option
case class Value(value: Any) extends Result

// answer to get-model, definitions of the declared functions together with
// auxiliary declarations and constraints, e.g. for the elements of uninterpreted sorts
case class Model(decls: List[Decl]) extends Result

sealed trait Cmd

sealed trait Ctrl extends Cmd
sealed trait Decl extends Cmd
sealed trait Query extends Cmd

case object CheckSat extends Query
// shares its name with the result Labels(labels) on purpose:
// the query (labels) is answered by (labels ...), the object doubles as the companion of the result
case object Labels extends Query
case object GetModel extends Query

case object Exit extends Throwable with Ctrl:
  override def toString =
    "Exit"

case class Push(depth: Int) extends Ctrl
case class Pop(depth: Int) extends Ctrl
case object Reset extends Ctrl

case class SetLogic(name: String) extends Decl

case class GetOption(name: String) extends Query
case class SetOption(name: String, value: Any) extends Decl

case class GetInfo(name: String) extends Query
case class SetInfo(name: String, value: Any) extends Decl

case class DeclareSort(con: Con, attrs: Attrs) extends Decl
case class DefineSort(con: Con, params: List[Param], body: Type, attrs: Attrs) extends Decl
// the constructors of a datatype together with their selectors
case class Datatype(params: List[Param], constrs: List[(Fun, List[Fun])])

// (mutually recursive) datatypes, where cons and datas correspond to each other
case class DeclareDatatypes(cons: List[Con], datas: List[Datatype], attrs: Attrs) extends Decl

case class DeclareFun(fun: Fun, attrs: Attrs) extends Decl
case class DefineFun(fun: Fun, body: Expr, attrs: Attrs) extends Decl

case class DeclareProc(proc: Proc, attrs: Attrs) extends Decl
case class DefineProc(proc: Proc, body: Prog, attrs: Attrs) extends Decl

sealed trait Justify
case object Axiom extends Justify
case object Goal extends Justify
case object Lemma extends Justify

case class Assert(justify: Justify, params: List[Param], phi: Expr, attrs: Attrs) extends Decl
