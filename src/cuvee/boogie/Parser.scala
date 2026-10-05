package cuvee.boogie

import util.Name
import cuvee.Error
import cuvee.core
import cuvee.core.State
import cuvee.core.Scope
import cuvee.core.Attrs

class Parser(var state: State):
  def resolve(scope: Scope, name: String): core.Param =
    state.types.param(name)

  def resolve(scope: Scope, formal: (String, Type)): core.Var =
    val (name, typ) = formal
    state.exprs.formal(name, resolve(scope, typ))

  def resolve(cmd: Cmd): List[core.Cmd] =
    cmd match
      case Axiom(params, attrs, expr) =>
        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        List(state.cmds.axiom(params_, phi_, attrs_))

      case Lemma(params, attrs, expr) =>
        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        List(state.cmds.lemma(params_, phi_, attrs_))

      // sorts with parameters are declared or defined generically
      case SortDef(attrs, name, params, alias) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)
        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val arity_ = params.length
        state = state.declare(name, arity_, attrs_)

        alias match
          case None =>
            val decl = state.cmds.declareSort(name)
            List(decl)

          case Some(typ) =>
            val typ_ = resolve(scope_, typ)
            state = state.define(name, params_, typ_)

            val defn = state.cmds.defineSort(name)
            List(defn)

      case ConstDef(attrs, consts) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)

        for (name, typ) <- consts
        yield
          val typ_ = resolve(scope, typ)
          state = state.declare(name, Nil, Nil, typ_, attrs_)
          state.cmds.declareFun(name, 0)

      case VarDef(attrs, vars) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)

        for (name, typ) <- vars
        yield
          val typ_ = resolve(scope, typ)
          state = state.declare(name, typ_, attrs_)
          state.cmds.declareVar(name)

      case FunDef(attrs, name, params, formals, typ, body) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)

        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val formals_ = formals.map(resolve(scope_, _))
        val typ_ = resolve(scope_, typ)
        val scope__ = scope_ ++ formals_

        val arity = formals_.length
        state = state.declare(name, params_, formals_, typ_, attrs_)

        body match
          case None =>
            val cmd_ = state.cmds.declareFun(name, arity)
            List(cmd_)

          case Some(expr) =>
            val expr_ = resolve(scope__, expr)
            val body_ = state.exprs.check(scope__, expr_, typ_)
            state = state.define(name, arity, body_)

            val cmd_ = state.cmds.defineFun(name, arity)
            List(cmd_)

      // procedures may read all global variables, and modify those in their modifies clauses,
      // the formal parameters shadow global variables of the same name
      case ProcDef(attrs, name, params, formals, rets, specs, body) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)

        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val formals_ = formals.map(resolve(scope_, _))
        val rets_ = rets.map(resolve(scope_, _))

        val globals = state.globals
        val scope__ = scope_ ++ globals ++ formals_ ++ rets_
        val contract_ = contract(scope__, specs)

        val mod = contract_.modifies.toSet
        val unknown = mod.filterNot(globals.contains)
        Error.report("modifies clause of procedure lists variables that are not global", name, unknown):
          require(unknown.isEmpty)

        state = state.declare(name, params_, formals_, rets_, Attrs(attrs_.attrs ++ contract_.attrs))

        body match
          case None =>
            val cmd_ = state.cmds.declareProc(name)
            List(cmd_)

          // the inputs of a procedure and the global variables that are not modified must not be assigned
          case Some(prog) =>
            val prog_ = resolve(scope__, mod, prog)
            val fixed = formals_.toSet ++ (globals.toSet -- mod)
            val body_ = state.progs.check(scope__, fixed, prog_)
            state = state.define(name, body_)

            val cmd_ = state.cmds.defineProc(name)
            List(cmd_)

  // an attribute with several arguments is repeated for each of them, {:a x, y} is {:a x} {:a y},
  // the arguments may be of any type
  def attributes(scope: Scope, attrs: List[Attr]): Attrs =
    val attrs_ =
      for
        Attr(name, args) <- attrs;
        arg <- if args.isEmpty then List(None) else args.map(arg => Some(term(scope, arg)))
      yield name -> arg

    Attrs(attrs_)

  def term(scope: Scope, expr: Expr) =
    val expr_ = resolve(scope, expr)
    val typ_ = core.Param("a").fresh
    state.exprs.check(scope, expr_, typ_)

  // the formula of an axiom or lemma is resolved and checked in the scope of its type parameters,
  // the type parameters of the assertion are these followed by those that remain in the formula otherwise
  def assertion(params: List[String], attrs: List[Attr], expr: Expr): (List[core.Param], core.Expr, Attrs) =
    val params_ = params.map(resolve(Scope.empty, _))
    val scope = Scope.empty ++ params_
    val attrs_ = attributes(scope, attrs)
    val phi_ = formula(scope, expr)
    (params_ ++ phi_.params.toList.filterNot(params_.contains), phi_, attrs_)

  def formula(scope: Scope, phi: Expr) =
    val expr_ = resolve(scope, phi)
    val typ_ = state.types.sort("Bool")
    state.exprs.check(scope, expr_, typ_)


  // the clauses of procedures and loops as attributes,
  // where each component of a lexicographic termination measure is an attribute decreases of its own
  def contract(scope: Scope, specs: List[Spec]): Attrs =
    val specs_ =
      specs.flatMap:
        case Requires(phi) =>
          List("requires" -> Some(formula(scope, phi)))

        case Ensures(phi) =>
          List("ensures" -> Some(formula(scope, phi)))

        case Invariant(phi) =>
          List("invariant" -> Some(formula(scope, phi)))

        case Modifies(xs) =>
          val unknown = xs.filterNot(scope.vars.contains(_))
          Error.report("unknown variables in modifies clause", scope, unknown):
            require(unknown.isEmpty)

          List("modifies" -> Some(xs.map(scope.vars(_))))

        case Decreases(exprs) =>
          for expr <- exprs
          yield "decreases" -> Some(measure(scope, expr))

    Attrs(specs_)

  def measure(scope: Scope, expr: Expr) =
    val expr_ = resolve(scope, expr)
    val typ_ = state.types.sort("Int")
    state.exprs.check(scope, expr_, typ_)

  def resolve(scope: Scope, typ: Type): core.Type =
    typ match
      case Sort(name, Nil) if scope.params.contains(name) =>
        scope.params(name)

      case Sort(name, args) if state.sorts.contains(name) =>
        val args_ = args.map(resolve(scope, _))
        state.types.sort(name, args_)

      case Array(index, value) =>
        val index_ = resolve(scope, index)
        val value_ = resolve(scope, value)
        state.types.sort("Array", List(index_, value_))

      case _ =>
        Error.raise("unknown type", typ, scope.params.keys, state.sorts.keys)

  // map selections and updates are applied from left to right
  def resolve(scope: Scope, base: core.Expr, access: List[Access]): core.Expr =
    access match
      case Nil =>
        base

      case Access(index, None) :: rest =>
        val index_ = resolve(scope, index)
        val base_ = state.exprs.app("select", List(base, index_))
        resolve(scope, base_, rest)

      case Access(index, Some(value)) :: rest =>
        val index_ = resolve(scope, index)
        val value_ = resolve(scope, value)
        val base_ = state.exprs.app("store", List(base, index_, value_))
        resolve(scope, base_, rest)

  def resolve(scope: Scope, expr: Expr): core.Expr =
    expr match
      case Dec(value) =>
        state.exprs.dec(util.Rational.decimal(value))

      case Num(value) =>
        state.exprs.num(BigInt(value))

      // backslashes escape the next character
      case Str(value) =>
        state.exprs.str(util.Strings.unescape(value))

      case App("!=", args, access) =>
        val expr_ = App("not", List(App("=", args, Nil)), access)
        resolve(scope, expr_)

      // the combinators of trace equation systems, whose bound variables are typed by the dependencies
      case Combinator("trace", Some(init), deps, acc :: bound, update) =>
        val init_ = resolve(scope, init)
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.trace(init_, deps_, acc, bound.map(util.Name(_, None))): (acc_, bound_) =>
          val scope_ = scope ++ (acc_ :: bound_)
          update.map((guard, result) => core.Upd(resolve(scope_, guard), resolve(scope_, result)))

      case Combinator("map", None, deps, bound, update) =>
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.map(deps_, bound.map(util.Name(_, None))): bound_ =>
          val scope_ = scope ++ bound_
          update.map((guard, result) => core.Upd(resolve(scope_, guard), resolve(scope_, result)))

      case Combinator("all", None, deps, bound, List((_, body))) =>
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.all(deps_, bound.map(util.Name(_, None))): bound_ =>
          resolve(scope ++ bound_, body)

      // the value at the entry of the procedure
      case App("old", List(arg), access) =>
        val base_ = state.exprs.old(resolve(scope, arg))
        resolve(scope, base_, access)

      case App(name, Nil, access) if scope.vars.contains(name) =>
        val base_ = scope.vars(name)
        resolve(scope, base_, access)

      case App(fun, args, access) if state.funs.contains((fun, args.length)) =>
        val args_ = args.map(resolve(scope, _))
        val base_ = state.exprs.app(fun, args_)
        resolve(scope, base_, access)

      case Butlast(arg) =>
        val arg_ = resolve(scope, arg)
        state.exprs.app(core.Fun.trace.butlast, List(arg_))

      case Ite(test, left, right) =>
        val test_ = resolve(scope, test)
        val left_ = resolve(scope, left)
        val right_ = resolve(scope, right)
        state.exprs.app("ite", List(test_, left_, right_))

      // triggers are ignored
      case Ex(bound, triggers, body) =>
        val bound_ = bound.map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.ex(bound_, body_)

      case All(bound, triggers, body) =>
        val bound_ = bound.map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.all(bound_, body_)

      case _ =>
        Error.raise("unknown expression", expr, scope.vars.keys, state.funs.keys)

  def variables(scope: Scope, names: List[String]): List[core.Var] =
    val unknown = names.filterNot(scope.vars.contains(_))
    Error.report("unknown variables", scope, unknown):
      require(unknown.isEmpty)

    names.map(scope.vars(_))

  // the assignment to an element a[i][j] := v is an update of the entire map a := a[i := a[i][j := v]]
  def update(base: core.Expr, indices: List[core.Expr], value: core.Expr): core.Expr =
    indices match
      case Nil =>
        value

      case index :: rest =>
        val inner = state.exprs.app("select", List(base, index))
        val value_ = update(inner, rest, value)
        state.exprs.app("store", List(base, index, value_))

  // `mod` are the global variables that may be modified by calls,
  // which are those in the modifies clause of the procedure and of the innermost loop
  def resolve(scope: Scope, mod: Set[core.Var], prog: Prog): core.Prog =
    prog match
      case Skip =>
        state.progs.skip

      case Break =>
        state.progs.break

      case Continue =>
        state.progs.continue

      case Return =>
        state.progs.return_

      // statements are type checked as part of the entire procedure body
      case Assume(phi) =>
        val phi_ = resolve(scope, phi)
        state.progs.assume(phi_)

      case Assert(phi) =>
        val phi_ = resolve(scope, phi)
        state.progs.assert(phi_)

      case Assign(lhs, rhs) =>
        Error.report("mismatching assignment", lhs, rhs):
          require(lhs.length == rhs.length)

        val lhs_ = variables(scope, lhs.map(_.name))
        val rhs_ =
          for (Lhs(_, indices), (x_, expr)) <- lhs zip (lhs_ zip rhs)
          yield update(x_, indices.map(resolve(scope, _)), resolve(scope, expr))

        state.progs.assign(lhs_, rhs_)

      case Havoc(names) =>
        val xs_ = variables(scope, names)
        state.progs.havoc(xs_)

      case Call(lhs, name, args) =>
        Error.report("procedure not declared", name):
          require(state.procs.contains(name))

        val callee = state.procattrs(name).modifies.toSet
        val unknown = callee -- mod
        Error.report("call modifies variables that are not in the modifies clause", name, unknown):
          require(unknown.isEmpty)

        val lhs_ = variables(scope, lhs)
        val args_ = args.map(resolve(scope, _))
        state.progs.call(name, args_, lhs_)

      case Block(locals, progs) =>
        val locals_ = locals.map(resolve(scope, _))
        val scope_ = scope ++ locals_
        val progs_ = progs.map(resolve(scope_, mod, _))
        state.progs.block(locals_, progs_)

      case If(Some(test), left, right) =>
        val test_ = resolve(scope, test)
        val left_ = resolve(scope, mod, left)
        val right_ = resolve(scope, mod, right)
        state.progs.if_(test_, left_, right_)

      case If(None, left, right) =>
        val left_ = resolve(scope, mod, left)
        val right_ = resolve(scope, mod, right)
        state.progs.choice(left_, right_)

      // calls in the body may modify the global variables in the modifies clause of the loop only,
      // which must be modifiable outside of the loop;
      // loops without test are nondeterministic iterations
      case While(test, specs, body) =>
        val attrs_ = contract(scope, specs)

        val mod_ = attrs_.modifies.toSet
        val nonglobal = mod_ -- state.globals
        Error.report("modifies clause of loop lists variables that are not global", nonglobal):
          require(nonglobal.isEmpty)

        val unknown = mod_ -- mod
        Error.report("modifies clause of loop lists global variables that are not modifiable", unknown):
          require(unknown.isEmpty)

        val body_ = resolve(scope, mod_, body)

        test match
          case Some(test) =>
            val test_ = resolve(scope, test)
            state.progs.while_(test_, body_, attrs_)

          case None =>
            state.progs.iter(body_, attrs_)
