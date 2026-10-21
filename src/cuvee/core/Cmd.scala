package cuvee.core

import util.Name
import cuvee.core._

trait Result

enum Ack extends Result:
  case Success
  case Unsupported
  // default answer to Done, which is not reported
  case Done

enum Status extends Result:
  case Unknown
  case Sat
  case Unsat
  case Correct
  case Incorrect

case class Labels(labels: List[String]) extends Result

case class Info(attrs: Attrs) extends Result
case class Value(value: Any) extends Result
case class Model(decls: List[Decl]) extends Result

sealed trait Cmd:
  def map(e: Expr => Expr, p: Prog => Prog): Cmd =
    this match
      case DeclareSort(con, attrs)              => DeclareSort(con, attrs.map(e))
      case DefineSort(con, params, body, attrs) => DefineSort(con, params, body, attrs.map(e))
      case DeclareDatatypes(cons, datas, attrs) => DeclareDatatypes(cons, datas, attrs.map(e))
      case DeclareFun(fun, attrs)               => DeclareFun(fun, attrs.map(e))
      case DefineFun(fun, body, attrs)          => DefineFun(fun, e(body), attrs.map(e))
      case DeclareVar(x, attrs)                 => DeclareVar(x, attrs.map(e))
      case DeclareProc(proc, attrs)             => DeclareProc(proc, attrs.map(e))
      case DefineProc(proc, body, attrs)        => DefineProc(proc, p(body), attrs.map(e))
      case Assert(justify, params, phi, attrs)  => Assert(justify, params, e(phi), attrs.map(e))
      case FuseFuns(term, rhs, attrs)           => FuseFuns(e(term), rhs.map(e), attrs.map(e))
      case AnnotateTag(tag, attrs)              => AnnotateTag(tag, attrs.map(e))
      case VerifyCall(proc, args)               => VerifyCall(proc, args.map(e))
      case _                                    => this

  def funs: Set[Fun] =
    this match
      case DeclareDatatypes(_, _, attrs) => attrs.funs
      case DeclareFun(_, attrs)          => attrs.funs
      case DefineFun(fun, body, attrs)   => body.funs ++ attrs.funs - fun
      case DeclareVar(_, attrs)          => attrs.funs
      case DeclareProc(_, attrs)         => attrs.funs
      case DefineProc(_, body, attrs)    => body.funs ++ attrs.funs
      case Assert(_, _, phi, attrs)      => phi.funs ++ attrs.funs
      case FuseFuns(term, rhs, attrs)    => term.funs ++ rhs.toList.funs ++ attrs.funs
      case AnnotateTag(_, attrs)         => attrs.funs
      case VerifyCall(_, args)           => args.funs
      case _                             => Set()

  // axioms, lemmas, and function definitions with the attribute :rw, which are rewrite rules of -simplify,
  // and function definitions with the attribute :fold, whose rules fold their body into a call (see Rules.from)
  def isRule: Boolean =
    this match
      case Assert(Axiom | Lemma, _, _, attrs) => attrs.contains("rw")
      case DefineFun(_, _, attrs)             => attrs.contains("rw") || attrs.contains("fold")
      case _                                  => false

sealed trait Ctrl extends Cmd
sealed trait Decl extends Cmd:
  def attrs: Attrs

sealed trait Query extends Cmd

case object CheckSat extends Query
case object Labels extends Query
case object GetModel extends Query
case object GetWitness extends Query

case object Exit extends Throwable with Ctrl:
  override def toString =
    "Exit"

// internal, marks the end of the input: stages flush their pending declarations,
// but nothing is printed or sent to a solver
case object Done extends Ctrl

case class Push(depth: Int) extends Ctrl
case class Pop(depth: Int) extends Ctrl
case object Reset extends Ctrl

case class SetLogic(name: String) extends Decl:
  def attrs = Attrs.empty

case class GetOption(name: String) extends Query
case class SetOption(name: String, value: Any) extends Decl:
  def attrs = Attrs.empty

case class GetInfo(name: String) extends Query
case class SetInfo(name: String, value: Any) extends Decl:
  def attrs = Attrs.empty

case class DeclareSort(con: Con, attrs: Attrs) extends Decl
case class DefineSort(con: Con, params: List[Param], body: Type, attrs: Attrs) extends Decl
case class Datatype(params: List[Param], constrs: List[(Fun, List[Fun])]):
  def sels: List[Fun] =
    constrs.flatMap(_._2)

case class DeclareDatatypes(cons: List[Con], datas: List[Datatype], attrs: Attrs) extends Decl

case class DeclareFun(fun: Fun, attrs: Attrs) extends Decl
case class DefineFun(fun: Fun, body: Expr, attrs: Attrs) extends Decl

case class DeclareVar(x: Var, attrs: Attrs) extends Decl

case class DeclareProc(proc: Proc, attrs: Attrs) extends Decl
case class DefineProc(proc: Proc, body: Prog, attrs: Attrs) extends Decl

case class AnnotateTag(tag: Name, attrs: Attrs) extends Decl

case class VerifyCall(proc: Name, args: List[Expr]) extends Query

sealed trait Justify
case object Axiom extends Justify
case object Goal extends Justify
case object Lemma extends Justify

case class Assert(justify: Justify, params: List[Param], phi: Expr, attrs: Attrs) extends Decl

// the request to fuse the composition `term` = g(f(x₁, ..., xₙ), y₁, ..., yₘ) of two defined functions into a single
// recursive function, whose variables are distinct, and which is the right-hand side `rhs` once the stage Fuse
// has processed it (see simplify.Fuse); Dafny only, written fuse term = ???
case class FuseFuns(term: Expr, rhs: Option[Expr], attrs: Attrs) extends Decl
