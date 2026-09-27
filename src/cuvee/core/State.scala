package cuvee.core

import cuvee.Name
import cuvee.Error
import cuvee.sexpr.Attrs

case class State(
    logic: Option[String] = None,
    options: Map[String, Any] = Map(),
    infos: Map[String, Any] = Map(),

    sorts: Map[Name, Con] = Map(),
    funs: Map[(Name, Int), Fun] = Map(),
    procs: Map[Name, Proc] = Map(),

    sortdefs: Map[Name, (List[Param], Type)] = Map(),
    fundefs: Map[(Name, Int), (List[Var], Expr)] = Map(),
    procdefs: Map[Name, (List[Var], List[Var], List[Var], List[Expr], List[Expr])] = Map(),

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

  def declare(con: Con, attrs: Attrs) =
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

  def declare(fun: Fun, attrs: Attrs) =
    val key = (fun.name, fun.arity)
    Error.report("function already declared", fun):
      require(!funs.contains(key))
    copy(funs = funs + (key -> fun))

  def define(fun: Fun, formals: List[Var], body: Expr) =
    val key = (fun.name, fun.arity)
    Error.report("function not declared", fun):
      require(funs.contains(key))
    Error.report("function already declared differently", fun):
      require(funs(key) == fun)
    Error.report("function already defined", fun):
      require(!fundefs.contains(key))
    copy(fundefs = fundefs + (key -> (formals, body)))

  def declare(proc: Proc, attrs: Attrs) =
    val name = proc.name
    Error.report("procedure already declared", proc):
      require(!procs.contains(name))
    copy(procs = procs + (name -> proc))

  def define(proc: Proc, in: List[Var], out: List[Var], mod: List[Var], pre: List[Expr], post: List[Expr]) =
    val name = proc.name
    Error.report("procedure not declared", proc):
      require(procs.contains(name))
    Error.report("procedure already declared differently", proc):
      require(procs(name) == proc)
    Error.report("procedure already defined", proc):
      require(!procdefs.contains(name))
    copy(procdefs = procdefs + (name -> (in, out, mod, pre, post)))

  def assert(cmd: Assert) =
    copy(asserts = asserts ++ List(cmd))

  def add(cmd: Decl): State =
    cmd match
      case SetLogic(name)           => setLogic(name)
      case SetOption(name, value)   => setOption(name, value)
      case DeclareSort(con, attrs)  => declare(con, attrs)
      case DeclareFun(fun, attrs)   => declare(fun, attrs)
      case DeclareProc(proc, attrs) => declare(proc, attrs)
      case cmd: Assert              => assert(cmd)

  def sort(name: Name, args: List[Type]) =
    Error.report("sort not declared", name):
      require(sorts.contains(name))

    val con = sorts(name)
    Sort(con, args)

  def formal(name: Name, typ: Type) =
    Var(name, typ)

  def num(value: BigInt) =
    Lit(value, Sort.int)

  def str(value: String) =
    Lit(value, Sort.string)

  def const(name: Name) =
    app(name, Nil)

  def app(name: Name, args: List[Expr]) =
    val key = (name, args.length)
    Error.report("function not declared", name):
      require(funs.contains(key))

    val fun = funs(key)
    val su = Subst.fresh(fun.params)
    val inst = su(fun.args)
    val typ = su(fun.res)
    App(fun, inst, typ, args)

  def all(bound: List[Var], body: Expr) =
    All(bound, body)

  def ex(bound: List[Var], body: Expr) =
    Ex(bound, body)

object State {
  // XXX: add SMT-LIB predefined
  def empty = State(None)
}
