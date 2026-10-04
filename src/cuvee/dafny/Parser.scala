package cuvee.dafny

import util.Name
import cuvee.Error
import cuvee.core
import cuvee.core.State
import cuvee.core.Scope
import cuvee.core.types
import cuvee.sexpr.Attrs

class Parser(var state: State):
  // val attrs_ = Attrs.empty

  // type check and resolve the overloaded operators, see Overload
  def check(scope: Scope, expr: core.Expr, typ: core.Type): core.Expr =
    val expr_ = state.exprs.check(scope, expr, typ)
    Overload(state, expr_)

  def check(scope: Scope, fixed: Set[core.Var], prog: core.Prog): core.Prog =
    val prog_ = state.progs.check(scope, fixed, prog)
    Overload(state, prog_)

  def resolve(scope: Scope, name: String): core.Param =
    state.types.param(name)

  def resolve(scope: Scope, formal: (String, Type)): core.Var =
    val (name, typ) = formal
    state.exprs.formal(name, resolve(scope, typ))

  def resolve(cmd: Cmd): List[core.Cmd] =
    cmd match
      case Axiom(expr) =>
        val scope = Scope.empty
        val expr_ = resolve(scope, expr)
        val typ_ = state.types.sort("Bool")
        val phi_ = check(scope, expr_, typ_)
        val params_ = phi_.params.toList

        val cmd_ = state.cmds.axiom(params_, phi_, Attrs.empty)
        List(cmd_)

      case SortDef(name, params, impl) =>
        val scope = Scope.empty
        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val arity_ = params.length
        state = state.declare(name, arity_, Attrs.empty)

        impl match
          case Left(None) =>
            val decl = state.cmds.declareSort(name)
            List(decl)

          case Left(Some(typ)) =>
            val typ_ = resolve(scope_, typ)
            state = state.define(name, params_, typ_)

            val defn = state.cmds.defineSort(name)
            List(defn)

          case Right(cmds) =>
            val decl = state.cmds.declareSort(name)

            val sort_ = state.types.sort(name, params_)
            val this_ = state.exprs.formal("this", sort_)

            val cmds_ =
              for
                cmd <- cmds;
                cmd_ <- resolve(scope_, name + "_", params_, List(this_), cmd)
              yield cmd_

            decl :: cmds_

      case DataDef(name, params, constrs, impl) =>
        val scope = Scope.empty
        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val arity_ = params.length
        state = state.declare(name, arity_, Attrs.empty)

        val sort_ = state.types.sort(name, params_)

        val constrs_ =
          for Constr(constr, sels) <- constrs
          yield
            val sels_ =
              for Sel(sel, arg) <- sels
              yield
                // selectors are qualified with the datatype like members, e.g. pair_fst,
                // such that datatypes may have selectors of the same name, e.g. the components 0, 1, ... of tuples
                val qname = name + "_" + sel
                val typ_ = resolve(scope_, arg)
                val this_ = state.exprs.formal("this", sort_)
                state = state.declare(qname, params_, List(this_), typ_, Attrs.empty)

                val sel_ = state.funs(qname, 1)
                sel_

            // the formal parameters of constructors are named after the selectors
            val formals_ =
              for sel_ <- sels_
              yield state.exprs.formal(sel_.name, sel_.res)

            val arity = formals_.length
            state = state.declare(constr, params_, formals_, sort_, Attrs.empty)

            val constr_ = state.funs((constr, arity))
            (constr_, sels_)

        state = state.define(name, core.Datatype(params_, constrs_))

        impl match
          case None =>
            val cmd_ = state.cmds.declareDatatype(name)
            List(cmd_)

          case Some(cmds) =>
            val decl = state.cmds.declareDatatype(name)

            val sort_ = state.types.sort(name, params_)
            val this_ = state.exprs.formal("this", sort_)

            val cmds_ =
              for
                cmd <- cmds;
                cmd_ <- resolve(scope_, name + "_", params_, List(this_), cmd)
              yield cmd_

            decl :: cmds_

      case _ =>
        resolve(Scope.empty, "", Nil, Nil, cmd)

  def formula(scope: Scope, phi: Expr) =
    val expr_ = resolve(scope, phi)
    val typ_ = state.types.sort("Bool")
    check(scope, expr_, typ_)

  def measure(scope: Scope, expr: Expr) =
    val expr_ = resolve(scope, expr)
    val typ_ = state.types.sort("Int")
    check(scope, expr_, typ_)

  def contract(scope: Scope, mod: List[List[String]], req: List[Expr], ens: List[Expr], dec: List[List[Expr]]) =
    val unknown = mod.flatten.filterNot(scope.vars.contains(_))
    Error.report("unknown variables in modifies clause", scope, unknown):
      require(unknown.isEmpty)

    val mod_ =
      for xs <- mod
      yield "modifies" -> Some(xs.map(scope.vars(_)))

    val req_ =
      for phi <- req
      yield "requires" -> Some(formula(scope, phi))

    val ens_ =
      for phi <- ens
      yield "ensures" -> Some(formula(scope, phi))

    Attrs(mod_ ++ req_ ++ ens_ ++ decreases(scope, dec))

  def invariants(scope: Scope, invs: List[Expr], dec: List[List[Expr]]) =
    val invs_ =
      for phi <- invs
      yield "invariant" -> Some(formula(scope, phi))

    Attrs(invs_ ++ decreases(scope, dec))

  // the components of a lexicographic termination measure in order, each of which is an integer
  def decreases(scope: Scope, dec: List[List[Expr]]) =
    for expr <- dec.flatten
    yield "decreases" -> Some(measure(scope, expr))

  def resolve(scope: Scope, prefix: String, outer_ : List[core.Param], self: List[core.Var], cmd: Cmd): List[core.Cmd] =
    cmd match
      case FunDef(fun, inner, formals, typ, req, ens, dec, body) =>
        val qname = prefix + fun

        val inner_ = inner.map(resolve(scope, _))
        val params_ = outer_ ++ inner_
        val scope_ = scope ++ inner_

        val formals_ = self ++ formals.map(resolve(scope_, _))

        val typ_ = resolve(scope_, typ)
        val scope__ = scope_ ++ formals_
        val attrs_ = contract(scope__, Nil, req, ens, dec)

        val arity = formals_.length
        state = state.declare(qname, params_, formals_, typ_, attrs_)

        body match
          case None =>
            val cmd_ = state.cmds.declareFun(qname, arity)
            List(cmd_)

          case Some(expr) =>
            val expr_ = resolve(scope__, expr)
            val body_ = check(scope__, expr_, typ_)
            state = state.define(qname, arity, body_)

            val cmd_ = state.cmds.defineFun(qname, arity)
            List(cmd_)

      case MethodDef(meth, inner, formals, rets, mod, req, ens, dec, body) =>
        val qname = prefix + meth

        val inner_ = inner.map(resolve(scope, _))
        val params_ = outer_ ++ inner_
        val scope_ = scope ++ inner_

        val formals_ = self ++ formals.map(resolve(scope_, _))
        val rets_ = rets.toList.flatten.map(resolve(scope_, _))

        val scope__ = scope_ ++ formals_ ++ rets_
        val attrs_ = contract(scope__, mod, req, ens, dec)
        state = state.declare(qname, params_, formals_, rets_, attrs_)

        body match
          case None =>
            val cmd_ = state.cmds.declareProc(qname)
            List(cmd_)

          case Some(prog) =>
            val prog_ = resolve(scope__, prog)
            // the inputs of a method must not be modified
            val body_ = check(scope__, formals_.toSet, prog_)
            state = state.define(qname, body_)

            val cmd_ = state.cmds.defineProc(qname)
            List(cmd_)

      case _ =>
        Error.raise("unsupported nested command", prefix, cmd)

  def resolve(scope: Scope, typ: Type): core.Type =
    typ match
      case Sort(name, Nil) if scope.params.contains(name) =>
        scope.params(name)

      case Sort(name, args) if state.sorts.contains(name) =>
        val args_ = args.map(resolve(scope, _))
        state.types.sort(name, args_)

      case _ =>
        Error.raise("unknown type", typ, scope.params.keys, state.sorts.keys)

  // members are looked up by the name of the type of `base`, which is resolved here,
  // since the type of an application may still be a fresh type parameter
  // fields of datatypes are their selectors, which are declared without the datatype as prefix
  def resolve(scope: Scope, base: core.Expr, access: List[Access]): core.Expr =
    access match
      case Nil =>
        base

      case Array(index, None) :: rest =>
        val index_ = resolve(scope, index)
        val base_ = state.exprs.app("select", List(base, index_))
        resolve(scope, base_, rest)

      case Array(index, Some(value)) :: rest =>
        val index_ = resolve(scope, index)
        val value_ = resolve(scope, value)
        val base_ = state.exprs.app("store", List(base, index_, value_))
        resolve(scope, base_, rest)

      // members are accessed on variables only, whose type is known without type checking
      case Member(fun, args) :: rest =>
        val self = base match
          case self: core.Var => self
          case _              => Error.raise("member access on an expression that is not a variable", base, fun)

        val qname = self.typ.name.name + "_" + fun

        args match
          case _ if state.funs.contains((qname, 1 + args.length)) =>
            val args_ = args.map(resolve(scope, _))
            val base_ = state.exprs.app(qname, self :: args_)
            resolve(scope, base_, rest)

          case _ if state.procs.contains(qname) =>
            Error.raise("method call not allowed here", self, qname, args)

          case _ =>
            Error.raise("invalid access", self, qname, access, scope, state.funs.keys, state.procs.keys)

  def resolve(scope: Scope, expr: Expr): core.Expr =
    expr match
      case Num(value) =>
        state.exprs.num(BigInt(value))

      case Dec(value) =>
        state.exprs.dec(util.Rational.decimal(value))

      case Str(value) =>
        state.exprs.str(value)

      case Tuple(List(arg)) =>
        resolve(scope, arg)

      // the constructors of tuples are declared in the prelude
      case Tuple(args) =>
        val args_ = args.map(resolve(scope, _))
        state.exprs.app("tuple" + args.length, args_)

      case App("!=", args, access) =>
        val expr_ = App("not", List(App("=", args, Nil)), access)
        resolve(scope, expr_)

      case Diff(xs, arg) =>
        val unknown = xs.filterNot(scope.vars.contains(_))
        Error.report("unknown variables of derivative", scope, unknown, xs):
          require(unknown.isEmpty)

        val xs_ = xs.map(scope.vars(_))
        val arg_ = resolve(scope, arg)
        state.exprs.diff(xs_, arg_)

      case App(name, Nil, access) if scope.vars.contains(name) =>
        val base_ = scope.vars(name)
        resolve(scope, base_, access)

      case App(fun, args, access) if state.funs.contains((fun, args.length)) =>
        val args_ = args.map(resolve(scope, _))
        val base_ = state.exprs.app(fun, args_)
        resolve(scope, base_, access)

      case Ite(test, left, right) =>
        val test_ = resolve(scope, test)
        val left_ = resolve(scope, left)
        val right_ = resolve(scope, right)
        state.exprs.app("ite", List(test_, left_, right_))

      case Ex(bound, body) =>
        val bound_ = bound.map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.ex(bound_, body_)

      case All(bound, body) =>
        val bound_ = bound.map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.all(bound_, body_)

      case Let(bound, args, body) =>
        Error.report("mismatching let", bound, args):
          require(bound.length == args.length)

        val args_ = args.map(resolve(scope, _))
        val bound_ = bound.map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.let(bound_, args_, body_)

      case _ =>
        Error.raise("unknown expression", expr, scope.vars.keys, state.funs.keys)

  def resolve(scope: Scope, prog: Prog): core.Prog =
    prog match
      case Skip =>
        state.progs.skip

      case Break =>
        state.progs.break

      case Continue =>
        state.progs.continue

      case Return =>
        state.progs.return_

      // statements are type checked as part of the entire method body
      case Assume(phi) =>
        val phi_ = resolve(scope, phi)
        state.progs.assume(phi_)

      case Assert(phi) =>
        val phi_ = resolve(scope, phi)
        state.progs.assert(phi_)

      // calls to top-level methods, with or without results
      case Assign(lhs, List(App(name, args, Nil))) if state.procs.contains(name) =>
        val unknown = lhs.filterNot(scope.vars.contains(_))
        Error.report("unknown local variables", scope, unknown, lhs):
          require(unknown.isEmpty)

        val lhs_ = lhs.map(scope.vars(_))
        val args_ = args.map(resolve(scope, _))
        state.progs.call(name, args_, lhs_)

      // all method calls must be top-level on variables
      case Assign(lhs, List(App(base, Nil, List(Member(fun, args))))) =>
        val unknown = (base :: lhs).filterNot(scope.vars.contains(_))
        Error.report("unknown local variables", scope, unknown):
          require(unknown.isEmpty)

        val lhs_ = lhs.map(scope.vars(_))
        val base_ = scope.vars(base)
        val qname = base_.typ.name.name + "_" + fun

        args match
          case _ if state.funs.contains((qname, 1 + args.length)) =>
            val args_ = args.map(resolve(scope, _))
            val rhs_ = List(state.exprs.app(qname, base_ :: args_))
            state.progs.assign(lhs_, rhs_)

          case _ if state.procs.contains(qname) =>
            val args_ = args.map(resolve(scope, _))
            state.progs.call(qname, base_ :: args_, lhs_)

          case _ =>
            Error.raise("invalid access", base, qname, fun, scope, state.funs.keys, state.procs.keys)

      case Assign(Nil, rhs) =>
        Error.raise("statement must be a method call", rhs)

      case Assign(lhs, rhs) =>
        val unknown = lhs.filterNot(scope.vars.contains(_))
        Error.report("unknown local variables", scope, unknown, lhs):
          require(unknown.isEmpty)

        val lhs_ = lhs.map(scope.vars(_))
        val rhs_ = rhs.map(resolve(scope, _))
        state.progs.assign(lhs_, rhs_)

      // locals must not shadow variables in scope, therefore their initial values
      // can be resolved together with the block as assignments at its beginning
      case Block(locals, progs) =>
        val locals_ = locals.flatMap(_.vars).map(resolve(scope, _))
        val shadowed = locals_.filter(x => scope.vars.contains(x.name))

        Error.report("local variables shadow variables in scope", shadowed):
          require(shadowed.isEmpty)

        val inits =
          for case Local(vars, Some(rhs)) <- locals
          yield Assign(vars.map(_._1), rhs)

        val scope_ = scope ++ locals_
        val progs_ = (inits ++ progs).map(resolve(scope_, _))
        state.progs.block(locals_, progs_)

      case If(Some(test), left, right) =>
        val test_ = resolve(scope, test)
        val left_ = resolve(scope, left)
        val right_ = resolve(scope, right)
        state.progs.if_(test_, left_, right_)

      case If(None, left, right) =>
        val left_ = resolve(scope, left)
        val right_ = resolve(scope, right)
        state.progs.choice(left_, right_)

      case While(Some(test), invs, dec, body) =>
        val test_ = resolve(scope, test)
        val body_ = resolve(scope, body)
        val attrs_ = invariants(scope, invs, dec)
        state.progs.while_(test_, body_, attrs_)

      case While(None, invs, dec, body) =>
        val body_ = resolve(scope, body)
        val attrs_ = invariants(scope, invs, dec)
        state.progs.iter(body_, attrs_)

      // the evolution constraint defaults to true
      case Ode(xs, rhs, dom, invs) =>
        val unknown = xs.filterNot(scope.vars.contains(_))
        Error.report("unknown local variables", scope, unknown, xs):
          require(unknown.isEmpty)

        val xs_ = xs.map(scope.vars(_))
        val rhs_ = rhs.map(resolve(scope, _))
        val dom_ = dom.map(resolve(scope, _)).getOrElse(core.True)
        val attrs_ = invariants(scope, invs, Nil)
        state.progs.ode(xs_, rhs_, dom_, attrs_)
