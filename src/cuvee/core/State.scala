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
    fundefs: Map[(Name, Int), Expr] = Map(),
    procdefs: Map[Name, Prog] = Map(),

    datatypes: Map[Name, Datatype] = Map(),

    asserts: List[Assert] = List()
    // XXX: add cache of further common things
):
  def hasFlag(name: String) =
    options.get(name) match
      case Some("true") => true
      case _            => false

  def setLogic(name: String) =
    Error.report("logic already set"):
      require(logic.isEmpty)

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

  def define(name: Name, data: Datatype) =
    val Datatype(params, constrs) = data

    Error.report("sort not declared", name):
      require(sorts.contains(name))
    Error.report("datatype already defined", name):
      require(!sortdefs.contains(name) && !datatypes.contains(name))

    val con = sorts(name)
    val sort = Sort(con, params)

    for (constr, sels) <- constrs
    do
      Error.report("constructor not declared", constr.name):
        val key = (constr.name, constr.args.length)
        require(funs.contains(key))
      Error.report("constructor has wrong result type", con, constr):
        require(constr.res == sort)
      Error.report("wrong selector types", constr, sels):
        require(constr.args == sels.map(_.res))

      for sel <- sels
      do
        Error.report("selector not declared", sel.name):
          val key = (sel.name, sel.args.length)
          require(funs.contains(key))
        Error.report("selector must take the datatype as its only argument", sel, sort):
          require(sel.args == List(sort))

    copy(datatypes = datatypes + (name -> data))

  def declare(name: Name, params: List[Param], formals: List[Var], res: Type, attrs: Attrs) =
    val arity = formals.length
    val key = (name, arity)

    Error.report("function already declared", key):
      require(!funs.contains(key))

    val fun = Fun(name, params, formals, res)
    copy(funs = funs + (key -> fun), funattrs = funattrs + (key -> attrs))

  // constructors and selectors of a datatype
  def declare(data: Datatype): State =
    val funs =
      for
        (constr, sels) <- data.constrs;
        fun <- constr :: sels
      yield fun

    funs.foldLeft(this):
      case (state, Fun(name, params, formals, res)) =>
        state.declare(name, params, formals, res, Attrs.empty)

  def define(name: Name, arity: Int, body: Expr) =
    val key = (name, arity)

    Error.report("function not declared", key):
      require(funs.contains(key))
    Error.report("function already defined", key):
      require(!fundefs.contains(key))

    copy(fundefs = fundefs + (key -> body))

  def declare(name: Name, params: List[Param], in: List[Var], out: List[Var], attrs: Attrs) =
    Error.report("procedure already declared", name):
      require(!procs.contains(name))

    val proc = Proc(name, params, in, out)
    copy(procs = procs + (name -> proc), procattrs = procattrs + (name -> attrs))

  def define(name: Name, body: Prog) =
    Error.report("procedure not declared", name):
      require(procs.contains(name))
    Error.report("procedure already defined", name):
      require(!procdefs.contains(name))

    copy(procdefs = procdefs + (name -> body))

  def add(cmd: Decl): State =
    cmd match
      case SetLogic(name) =>
        setLogic(name)

      case SetOption(name, value) =>
        setOption(name, value)

      case SetInfo(name, value) =>
        setInfo(name, value)

      case DeclareSort(Con(name, arity), attrs) =>
        declare(name, arity, attrs)

      // all sorts are declared first since they may occur in each others' constructors
      case DeclareDatatypes(cons, datas) =>
        Error.report("mismatching datatype declarations", cons, datas):
          require(cons.length == datas.length)

        val state =
          cons.foldLeft(this):
            case (state, Con(name, arity)) =>
              state.declare(name, arity, Attrs.empty)

        (cons zip datas).foldLeft(state):
          case (state, (Con(name, _), data)) =>
            state.declare(data).define(name, data)

      case DefineSort(Con(name, arity), params, body, attrs) =>
        declare(name, arity, attrs).define(name, params, body)

      case DeclareFun(Fun(name, params, formals, res), attrs) =>
        declare(name, params, formals, res, attrs)

      case DefineFun(Fun(name, params, formals, res), body, attrs) =>
        declare(name, params, formals, res, attrs).define(name, formals.length, body)

      case DeclareProc(Proc(name, params, in, out), attrs) =>
        declare(name, params, in, out, attrs)

      case DefineProc(Proc(name, params, in, out), body, attrs) =>
        declare(name, params, in, out, attrs).define(name, body)

      case cmd: Assert =>
        copy(asserts = asserts :+ cmd)

  object types:
    def param(name: Name) =
      Param(name)

    def sort(name: Name, args: List[Type] = Nil) =
      Error.report("sort not declared", name):
        require(sorts.contains(name))

      val con = sorts(name)
      Error.report("wrong number of sort arguments", name, con.arity, args):
        require(con.arity == args.length)

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
      Type.check(State.this, scope, expr, typ)

  object progs:
    def check(scope: Scope, fixed: Set[Var], prog: Prog) =
      Type.check(State.this, scope, fixed, prog)

    def skip = Block(Nil, Nil)
    def break = Break
    def continue = Continue
    def return_ = Return

    def havoc(xs: List[Var]) =
      Spec.havoc(xs)

    def assume(phi: Expr) =
      Spec.assume(phi)

    def assert(phi: Expr) =
      Spec.assert(phi)

    def assign(lhs: List[Var], rhs: List[Expr]) =
      Assign(lhs, rhs)

    def call(proc: Name, args: List[Expr], res: List[Var]) =
      Call(proc, args, res)

    def block(locals: List[Var], progs: List[Prog]) =
      Block(locals, progs)

    def if_(test: Expr, left: Prog, right: Prog) =
      If(test, left, right)

    def while_(test: Expr, body: Prog, attrs: Attrs) =
      While(test, body, attrs)

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

    def declareDatatype(name: Name) =
      val con = sorts(name)
      val data = datatypes(name)
      DeclareDatatypes(List(con), List(data))

    def declareFun(name: Name, arity: Int) =
      val key = (name, arity)
      val fun = funs(key)
      val attrs = funattrs(key)
      DeclareFun(fun, attrs)

    def defineFun(name: Name, arity: Int) =
      val key = (name, arity)
      val fun = funs(key)
      val attrs = funattrs(key)
      val body = fundefs(key)
      DefineFun(fun, body, attrs)

    def declareProc(name: Name) =
      val proc = procs(name)
      val attrs = procattrs(name)
      DeclareProc(proc, attrs)

    def defineProc(name: Name) =
      val proc = procs(name)
      val attrs = procattrs(name)
      val body = procdefs(name)
      DefineProc(proc, body, attrs)

    def axiom(params: List[Param], phi: Expr, attrs: Attrs) =
      Assert(Axiom, params, phi, attrs)

    def lemma(params: List[Param], phi: Expr, attrs: Attrs) =
      Assert(Lemma, params, phi, attrs)

    def goal(params: List[Param], phi: Expr, attrs: Attrs) =
      Assert(Goal, params, phi, attrs)

object State {
  def empty = State(None)
}
