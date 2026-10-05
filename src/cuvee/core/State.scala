package cuvee.core

import util.Name
import util.Rational
import cuvee.Error

// the declarations and definitions so far, by kind and name, with their attributes and the assertions,
// together with builders for types, expressions, programs, and commands, which the frontends use (see style.md);
// functions are identified by name and arity, since the frontends may overload names with different arities;
// a declaration or definition that coincides with an existing one is accepted and leaves the state unchanged,
// e.g. those of the prelude of a frontend in printed output that is parsed again (see cuvee.pipe.Source)
case class State(
    logic: Option[String] = None,
    options: Map[String, Any] = Map(),
    infos: Map[String, Any] = Map(),

    sorts: Map[Name, Con] = Map(),
    funs: Map[(Name, Int), Fun] = Map(),
    vars: Map[Name, Var] = Map(),
    procs: Map[Name, Proc] = Map(),

    sortattrs: Map[Name, Attrs] = Map(),
    funattrs: Map[(Name, Int), Attrs] = Map(),
    varattrs: Map[Name, Attrs] = Map(),
    procattrs: Map[Name, Attrs] = Map(),

    sortdefs: Map[Name, (List[Param], Type)] = Map(),
    fundefs: Map[(Name, Int), Expr] = Map(),
    procdefs: Map[Name, Prog] = Map(),

    datatypes: Map[Name, Datatype] = Map(),

    asserts: List[Assert] = List()
):
  // whether the option `name` is set to true
  // `f` unless the declaration or definition coincides with the existing one, which leaves the state unchanged
  def unless(same: Boolean)(f: => State): State =
    if same then this else f

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

  def declare(name: Name, arity: Int, attrs: Attrs): State =
    unless(sorts.get(name) == Some(Con(name, arity))):
      Error.report("sort already declared", name):
        require(!sorts.contains(name))

      val con = Con(name, arity)
      copy(sorts = sorts + (name -> con), sortattrs = sortattrs + (name -> attrs))

  def define(name: Name, params: List[Param], body: Type): State =
    unless(sortdefs.get(name) == Some((params, body))):
      Error.report("sort not declared", name):
        require(sorts.contains(name))
      Error.report("sort already defined", name):
        require(!sortdefs.contains(name))

      copy(sortdefs = sortdefs + (name -> (params, body)))

  def define(name: Name, data: Datatype): State =
    unless(datatypes.get(name) == Some(data)):
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

  def declare(name: Name, params: List[Param], formals: List[Var], res: Type, attrs: Attrs): State =
    val arity = formals.length
    val key = (name, arity)

    unless(funs.get(key) == Some(Fun(name, params, formals, res))):
      Error.report("function already declared", key):
        require(!funs.contains(key))

      val fun = Fun(name, params, formals, res)
      copy(funs = funs + (key -> fun), funattrs = funattrs + (key -> attrs))

  // the constructors of all datatypes by name
  def constrs: Map[Name, Fun] =
    val all =
      for
        data <- datatypes.values
        (constr, _) <- data.constrs
      yield constr.name -> constr

    all.toMap

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

  def define(name: Name, arity: Int, body: Expr): State =
    val key = (name, arity)

    unless(fundefs.get(key) == Some(body)):
      Error.report("function not declared", key):
        require(funs.contains(key))
      Error.report("function already defined", key):
        require(!fundefs.contains(key))

      copy(fundefs = fundefs + (key -> body))

  // the global variables, whose order is fixed since the state does not change during a transformation
  def globals: List[Var] =
    vars.values.toList

  def declare(name: Name, typ: Type, attrs: Attrs): State =
    unless(vars.get(name) == Some(Var(name, typ))):
      Error.report("variable already declared", name):
        require(!vars.contains(name))

      val x = Var(name, typ)
      copy(vars = vars + (name -> x), varattrs = varattrs + (name -> attrs))

  def declare(name: Name, params: List[Param], in: List[Var], out: List[Var], attrs: Attrs): State =
    unless(procs.get(name) == Some(Proc(name, params, in, out))):
      Error.report("procedure already declared", name):
        require(!procs.contains(name))

      // the precondition is evaluated at the entry, where there are no other values to refer to
      Error.report("precondition refers to old values", name):
        require(!Old.occurs(attrs.requires))

      val proc = Proc(name, params, in, out)
      copy(procs = procs + (name -> proc), procattrs = procattrs + (name -> attrs))

  def define(name: Name, body: Prog): State =
    unless(procdefs.get(name) == Some(body)):
      Error.report("procedure not declared", name):
        require(procs.contains(name))
      Error.report("procedure already defined", name):
        require(!procdefs.contains(name))

      copy(procdefs = procdefs + (name -> body))

  // the state with the declaration or definition of `cmd`, which must not be declared already
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
      case DeclareDatatypes(cons, datas, attrs) =>
        Error.report("mismatching datatype declarations", cons, datas):
          require(cons.length == datas.length)

        val state =
          cons.foldLeft(this):
            case (state, Con(name, arity)) =>
              state.declare(name, arity, attrs)

        (cons zip datas).foldLeft(state):
          case (state, (Con(name, _), data)) =>
            state.declare(data).define(name, data)

      case DefineSort(Con(name, arity), params, body, attrs) =>
        declare(name, arity, attrs).define(name, params, body)

      case DeclareFun(Fun(name, params, formals, res), attrs) =>
        declare(name, params, formals, res, attrs)

      case DefineFun(Fun(name, params, formals, res), body, attrs) =>
        declare(name, params, formals, res, attrs).define(name, formals.length, body)

      case DeclareVar(Var(name, typ), attrs) =>
        declare(name, typ, attrs)

      case DeclareProc(Proc(name, params, in, out), attrs) =>
        declare(name, params, in, out, attrs)

      case DefineProc(Proc(name, params, in, out), body, attrs) =>
        declare(name, params, in, out, attrs).define(name, body)

      case cmd: Assert =>
        copy(asserts = asserts :+ cmd)

  // types, where sorts must be declared with the right number of arguments
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

  // expressions, where applications instantiate the type parameters of the functions freshly,
  // which are determined by type checking (see check)
  object exprs:
    def formal(name: Name, typ: Type) =
      Var(name, typ)

    def num(value: BigInt) =
      Lit(value, Sort.int)

    def dec(value: Rational) =
      Lit(value, Sort.real)

    def str(value: String) =
      Lit(value, Sort.string)

    def const(name: Name) =
      app(name, Nil)

    def app(name: Name, args: List[Expr]): App =
      val key = (name, args.length)
      Error.report("function not declared", name):
        require(funs.contains(key))

      app(funs(key), args)

    // applications of built-in functions that need not be declared, e.g. those on sequences
    def app(fun: Fun, args: List[Expr]): App =
      val su = Subst.fresh(fun.params)
      val inst = su(fun.args)
      val typ = su(fun.res)
      App(fun, inst, typ, args)

    def all(bound: List[Var], body: Expr) =
      All(bound, body)

    def ex(bound: List[Var], body: Expr) =
      Ex(bound, body)

    // whether `expr` is built by constructor `name`
    def is(expr: Expr, name: Name) =
      Error.report("constructor not declared", name):
        require(constrs.contains(name))
      Is(expr, constrs(name))

    def as(expr: Expr, typ: Type) =
      As(expr, typ)

    // the combinators of trace equation systems, whose bound variables have the types of the elements of the dependencies,
    // and the accumulator that of the initial value; the update or body is resolved with the bound variables
    def trace(init: Expr, deps: List[Expr], acc: Name, bound: List[Name])(updates: (Var, List[Var]) => List[Upd]): Trace =
      Error.report("mismatching dependencies and bound variables", deps, bound):
        require(deps.length == bound.length)
      val acc_ = Var(acc, init.typ)
      val bound_ = for (x, dep) <- bound zip deps yield Var(x, Type.elem(dep.typ))
      Trace(init, deps, acc_, bound_, updates(acc_, bound_))

    def map(deps: List[Expr], bound: List[Name])(updates: List[Var] => List[Upd]): Maps =
      Error.report("mismatching dependencies and bound variables", deps, bound):
        require(deps.length == bound.length)
      val bound_ = for (x, dep) <- bound zip deps yield Var(x, Type.elem(dep.typ))
      Maps(deps, bound_, updates(bound_))

    def all(deps: List[Expr], bound: List[Name])(body: List[Var] => Expr): Invs =
      Error.report("mismatching dependencies and bound variables", deps, bound):
        require(deps.length == bound.length)
      val bound_ = for (x, dep) <- bound zip deps yield Var(x, Type.elem(dep.typ))
      Invs(deps, bound_, body(bound_))

    // the value of `expr` at the entry of the enclosing procedure
    def old(expr: Expr) =
      Old(expr)

    def diff(xs: List[Var], expr: Expr) =
      Diff(xs, expr)

    def let(bound: List[Var], args: List[Expr], body: Expr) =
      Error.report("invalid let binding", bound, args):
        require(bound.length == args.length)
      Let(bound, args, body)

    def match_(arg: Expr, cases: List[Case]) =
      Error.report("match without cases", arg):
        require(cases.nonEmpty)
      Match(arg, cases)

    // type checking resolves the overloaded operators, see Overload
    def check(scope: Scope, expr: Expr, typ: Type) =
      Overload(State.this, Type.check(State.this, scope, expr, typ))

  // programs, which are type checked as a whole by `check`
  object progs:
    def check(scope: Scope, fixed: Set[Var], prog: Prog) =
      Overload(State.this, Type.check(State.this, scope, fixed, prog))

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

    // chains of choices are flattened, if * { a } else if * { b } else { c }
    def choice(left: Prog, right: Prog) =
      right match
        case Choice(progs) => Choice(left :: progs)
        case _             => Choice(List(left, right))

    def while_(test: Expr, body: Prog, attrs: Attrs) =
      While(test, body, attrs)

    def iter(body: Prog, attrs: Attrs) =
      Iter(body, attrs)

    def ode(xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs) =
      Error.report("mismatching differential equations", xs, rhs):
        require(xs.length == rhs.length)
      Ode(xs, rhs, dom, attrs)

    def par(calls: List[Call]) =
      Par(calls)

  // the commands for the declarations and definitions of the state by name, with their attributes
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
      declareDatatypes(List(name))

    // mutually recursive datatypes, whose attributes are those of the first one
    def declareDatatypes(names: List[Name]) =
      val cons = names.map(sorts(_))
      val attrs = sortattrs(names.head)
      val datas = names.map(datatypes(_))
      DeclareDatatypes(cons, datas, attrs)

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

    def declareVar(name: Name) =
      val x = vars(name)
      val attrs = varattrs(name)
      DeclareVar(x, attrs)

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

object State:
  def empty = State(None)
