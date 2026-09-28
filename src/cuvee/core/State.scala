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

    sortattrs: Map[Name, Attrs] = Map(),
    funattrs: Map[(Name, Int), Attrs] = Map(),
    procattrs: Map[Name, Attrs] = Map(),

    sortdefs: Map[Name, (List[Param], Type)] = Map(),
    fundefs: Map[(Name, Int), (List[Var], Expr)] = Map(),
    procdefs: Map[Name, (List[Var], List[Var], Prog)] = Map(),

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

  def declare(name: Name, arity: Int, attrs: Attrs) =
    Error.report("sort already declared", name):
      require(!sorts.contains(name))

    val con = Con(name, arity)
    copy(sorts = sorts + (name -> con), sortattrs = sortattrs + (name -> attrs))

  def define(name: Name, params: List[Param], body: Type) =
    Error.report("sort not declared", name):
      require(sorts.contains(name))
    Error.report("sort already defined", name):
      require(!sortdefs.contains(name))

    copy(sortdefs = sortdefs + (name -> (params, body)))

  def declare(name: Name, params: List[Param], args: List[Type], res: Type, attrs: Attrs) =
    val arity = args.length
    val key = (name, arity)

    Error.report("function already declared", key):
      require(!funs.contains(key))

    val fun = Fun(name, params, args, res)
    copy(funs = funs + (key -> fun), funattrs = funattrs + (key -> attrs))

  def define(name: Name, formals: List[Var], body: Expr) =
    val arity = formals.length
    val key = (name, arity)

    Error.report("function not declared", key):
      require(funs.contains(key))
    Error.report("function already defined", key):
      require(!fundefs.contains(key))

    copy(fundefs = fundefs + (key -> (formals, body)))

  def declare(name: Name, params: List[Param], in: List[Type], out: List[Type], attrs: Attrs) =
    Error.report("procedure already declared", name):
      require(!procs.contains(name))

    val proc = Proc(name, params, in, out)
    copy(procs = procs + (name -> proc), procattrs = procattrs + (name -> attrs))

  def define(name: Name, in: List[Var], out: List[Var], body: Prog) =
    Error.report("procedure not declared", name):
      require(procs.contains(name))
    Error.report("procedure already defined", name):
      require(!procdefs.contains(name))

    copy(procdefs = procdefs + (name -> (in, out, body)))

  def add(cmd: Decl): State =
    cmd match
      case SetLogic(name) =>
        setLogic(name)

      case SetOption(name, value) =>
        setOption(name, value)

      case DeclareSort(Con(name, arity), attrs) =>
        declare(name, arity, attrs)

      case DefineSort(Con(name, arity), params, body, attrs) =>
        declare(name, arity, attrs).define(name, params, body)

      case DeclareFun(Fun(name, params, args, res), attrs) =>
        declare(name, params, args, res, attrs)

      case DefineFun(Fun(name, params, args, res), formals, body, attrs) =>
        declare(name, params, args, res, attrs).define(name, formals, body)

      case DeclareProc(Proc(name, params, in, out), attrs) =>
        declare(name, params, in, out, attrs)

      case DefineProc(Proc(name, params, in, out), args, ret, body, attrs) =>
        declare(name, params, in, out, attrs).define(name, args, ret, body)

  object types:
    def param(name: Name) =
      Param(name)

    def sort(name: Name, args: List[Type] = Nil) =
      Error.report("sort not declared", name):
        require(sorts.contains(name))

      val con = sorts(name)
      Sort(con, args)

  object exprs:
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

    def let(bound: List[Var], args: List[Expr], body: Expr) =
      Error.report("invalid let binding", bound, args):
        require(bound.length == args.length)
      Let(bound, args, body)

    def check(scope: Scope, expr: Expr, typ: Type) =
      Type.check(scope, expr, typ)

  object cmds:
    def declareSort(name: Name) =
      val con = sorts(name)
      val attrs = sortattrs(name)
      DeclareSort(con, attrs)

    def defineSort(name: Name) =
      val con = sorts(name)
      val attrs = sortattrs(name)
      val (params, body) = sortdefs(name)
      DefineSort(con, params, body, attrs)

    def declareFun(name: Name, arity: Int) =
      val key = (name, arity)
      val fun = funs(key)
      val attrs = funattrs(key)
      DeclareFun(fun, attrs)

    def defineFun(name: Name, arity: Int) =
      val key = (name, arity)
      val fun = funs(key)
      val attrs = funattrs(key)
      val (formals, body) = fundefs(key)
      DefineFun(fun, formals, body, attrs)

    def declareProc(name: Name) =
      val proc = procs(name)
      val attrs = procattrs(name)
      DeclareProc(proc, attrs)

    def defineProc(name: Name) =
      val proc = procs(name)
      val attrs = procattrs(name)
      val (in, out, body) = procdefs(name)
      DefineProc(proc, in, out, body, attrs)

    def axiom(params: List[Param], phi: Expr, attrs: Attrs) =
      Assert(Axiom, params, phi, attrs)

    def lemma(params: List[Param], phi: Expr, attrs: Attrs) =
      Assert(Lemma, params, phi, attrs)

    def goal(params: List[Param], phi: Expr, attrs: Attrs) =
      Assert(Goal, params, phi, attrs)

object State {
  // XXX: add SMT-LIB predefined
  def empty = State(None)
}
