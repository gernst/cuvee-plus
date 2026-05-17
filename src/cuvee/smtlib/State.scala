package cuvee.smtlib

import cuvee.Name
import cuvee.Error

import cuvee.pure._
import cuvee.prog._
import cuvee.smtlib._

case class State(
    logic: Option[String] = None,
    options: Map[String, Any] = Map(),

    sorts: Map[Name, Con] = Map(),
    funs: Map[Name, Fun] = Map(),
    procs: Map[Name, Proc] = Map(),

    sortdefs: Map[Name, Sort] = Map(),
    fundefs: Map[Name, Expr] = Map(),
    procdefs: Map[Name, Body] = Map(),

    asserts: List[Assert] = List()
    // XXX: add cache of further common things
):
  def hasFlag(name: String) =
    options.get(name) match
      case Some("true") => true
      case _            => false

  def setLogic(name: String) =
    Error.reportIf("logic already set", logic.nonEmpty)
    copy(logic = Some(name))

  def setOption(name: String, value: Any) =
    copy(options = options + (name -> value))

  def declare(con: Con) =
    val name = con.name
    Error.reportIf("sort already declared", sorts.contains(name))
    copy(sorts = sorts + (name -> con))

  def declare(fun: Fun) =
    val name = fun.name
    Error.reportIf("function already declared", funs.contains(name))
    copy(funs = funs + (name -> fun))

  def declare(proc: Proc) =
    val name = proc.name
    Error.reportIf("procedure already declared", procs.contains(name))
    copy(procs = procs + (name -> proc))

  def assert(cmd: Assert) =
    copy(asserts = asserts ++ List(cmd))

  def add(cmd: Decl): State =
    cmd match
      case SetLogic(name)         => setLogic(name)
      case SetOption(name, value) => setOption(name, value)
      case DeclareSort(con)       => declare(con)
      case DeclareFun(fun)        => declare(fun)
      case DeclareProc(proc)      => declare(proc)
      case cmd: Assert            => assert(cmd)

object State {
  // XXX: add SMT-LIB predefined
  def default = State(???)
}
