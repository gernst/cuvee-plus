package cuvee.core

import cuvee.Name
import cuvee.Error

case class State(
    logic: Option[String] = None,
    options: Map[String, Any] = Map(),
    infos: Map[String, Any] = Map(),

    sorts: Map[Name, Con] = Map(),
    funs: Map[Name, Fun] = Map(),
    // procs: Map[Name, Proc] = Map(),

    sortdefs: Map[Name, (List[Param], Type)] = Map(),
    fundefs: Map[Name, (List[Var], Expr)] = Map(),
    // procdefs: Map[Name, Body] = Map(),

    asserts: List[Assert] = List()
    // XXX: add cache of further common things
):
  def hasFlag(name: String) =
    options.get(name) match
      case Some("true") => true
      case _            => false

  def setLogic(name: String) =
    Error.report("logic already set"):
      require(logic.nonEmpty)
    copy(logic = Some(name))

  def setOption(name: String, value: Any) =
    copy(options = options + (name -> value))

  def setInfo(name: String, value: Any) =
    copy(infos = infos + (name -> value))

  def declare(con: Con) =
    val name = con.name
    Error.report("sort already declared", con):
      require(!sorts.contains(name))
    copy(sorts = sorts + (name -> con))

  def define(con: Con, params: List[Param], body: Type) =
    val name = con.name
    Error.report("sort not declared", con):
      require(sorts.contains(name))
    Error.report("sort already declared differently", con):
      require(sorts(name) == con)
    Error.report("sort already defined", con):
      require(!sortdefs.contains(name))
    copy(sortdefs = sortdefs + (name -> (params, body)))

  def declare(fun: Fun) =
    val name = fun.name
    Error.report("function already declared", fun):
      require(!funs.contains(name))
    copy(funs = funs + (name -> fun))

  def define(fun: Fun, formals: List[Var], body: Expr) =
    val name = fun.name
    Error.report("function not declared", fun):
      require(funs.contains(name))
    Error.report("function already declared differently", fun):
      require(funs(name) == fun)
    Error.report("function already defined", fun):
      require(!fundefs.contains(name))
    copy(fundefs = fundefs + (name -> (formals, body)))

  // def declare(proc: Proc) =
  //   val name = proc.name
  //   Error.reportIf("procedure already declared", procs.contains(name))
  //   copy(procs = procs + (name -> proc))

  def assert(cmd: Assert) =
    copy(asserts = asserts ++ List(cmd))

  def add(cmd: Decl): State =
    cmd match
      case SetLogic(name)         => setLogic(name)
      case SetOption(name, value) => setOption(name, value)
      case DeclareSort(con)       => declare(con)
      case DeclareFun(fun)        => declare(fun)
      // case DeclareProc(proc)      => declare(proc)
      case cmd: Assert => assert(cmd)

object State {
  // XXX: add SMT-LIB predefined
  def default = State(None).declare(Con.int)
}
