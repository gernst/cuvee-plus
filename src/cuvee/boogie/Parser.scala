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

      // the selectors are not qualified with the datatype, unlike in Dafny, since Boogie has no member access,
      // hence they must be unique like in SMT-LIB;
      // the sorts of mutually recursive datatypes are declared first, such that the constructors may refer to all of them
      case DataDef(attrs, datas) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)

        for Data(name, params, _) <- datas
        do state = state.declare(name, params.length, attrs_)

        for Data(name, params, constrs) <- datas
        do
          val params_ = params.map(resolve(scope, _))
          val scope_ = scope ++ params_
          val sort_ = state.types.sort(name, params_)

          val constrs_ =
            for Constr(constr, sels) <- constrs
            yield
              val sels_ =
                for Sel(sel, arg) <- sels
                yield
                  val typ_ = resolve(scope_, arg)
                  val this_ = state.exprs.formal("this", sort_)
                  state = state.declare(sel, params_, List(this_), typ_, Attrs.empty)
                  state.funs((sel, 1))

              // the formal parameters of constructors are numbered as in SMT-LIB, such that they coincide with the
              // built-in constructors (see core.Fun)
              val formals_ = core.Expr.vars("x", sels_.map(_.res))

              state = state.declare(constr, params_, formals_, sort_, Attrs.empty)
              (state.funs((constr, formals_.length)), sels_)

          state = state.define(name, core.Datatype(params_, constrs_))

        // the names as declared above, where a subscript is an index, e.g. tuple₁ of the prelude of Dafny
        List(state.cmds.declareDatatypes(datas.map(data => (data.name: Name))))

      case ConstDef(attrs, consts) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)

        for (name, typ) <- flatten(consts)
        yield
          val typ_ = resolve(scope, typ)
          state = state.declare(name, Nil, Nil, typ_, attrs_)
          state.cmds.declareFun(name, 0)

      case VarDef(attrs, vars) =>
        val scope = Scope.empty
        val attrs_ = attributes(scope, attrs)

        for (name, typ) <- flatten(vars)
        yield
          val typ_ = resolve(scope, typ)
          state = state.declare(name, typ_, attrs_)
          state.cmds.declareVar(name)

      case FunDef(attrs, name, params, formals, typ, body) =>
        val scope = Scope.empty

        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val formals_ = flatten(formals).map(resolve(scope_, _))
        val typ_ = resolve(scope_, typ)
        val scope__ = scope_ ++ formals_
        val attrs_ = implementation(name, scope, scope__, List(typ_), attrs)

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

        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val formals_ = flatten(formals).map(resolve(scope_, _))
        val rets_ = flatten(rets).map(resolve(scope_, _))
        val attrs_ = implementation(name, scope, scope_ ++ formals_, rets_.map(_.typ), attrs)

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
            val prog_ = resolve(scope__, prog)
            val fixed = formals_.toSet ++ (globals.toSet -- mod)
            val body_ = state.progs.check(scope__, fixed, mod, prog_)
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

  // the attributes of a function or procedure `name`, resolved in `scope`, except the pattern of {:implement}, by which
  // it names the function that it implements and the positions of its arguments, an application to its inputs in
  // `inputs`, of the type of its single result, the result of a function or the output of a procedure, among
  // `results` (see transform.Implement)
  def implementation(name: String, scope: Scope, inputs: Scope, results: List[core.Type], attrs: List[Attr]): Attrs =
    val attrs_ =
      for attr <- attrs
      yield attr match
        case Attr("implement", List(pattern)) =>
          Error.report("an implementation with {:implement pattern} has a single result", name):
            require(results.length == 1)
          Error.report("the pattern of {:implement} does not have the result type of the implementation", name):
            Attrs(List("implement" -> Some(state.exprs.check(inputs, resolve(inputs, pattern), results.head))))

        case _ =>
          attributes(scope, List(attr))

    Attrs(attrs_.flatMap(_.attrs))

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
          Error.report("unknown variables in modifies clause", unknown):
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

      // the nested arrays of the indices (see core.Arrays)
      case Array(indices, value) =>
        val indices_ = indices.map(resolve(scope, _))
        val value_ = resolve(scope, value)
        indices_.foldRight(value_)((index_, inner) => state.types.sort("Array", List(index_, inner)))

      case _ =>
        Error.raise("unknown type", typ)

  // map selections and updates are applied from left to right
  def resolve(scope: Scope, base: core.Expr, access: List[Selector]): core.Expr =
    access match
      case Nil =>
        base

      // a[i, j] is a[i][j] of the nested arrays (see core.Arrays)
      case Access(indices, None) :: rest =>
        val indices_ = indices.map(resolve(scope, _))
        val base_ = indices_.foldLeft(base)((inner, index_) => state.exprs.app("select", List(inner, index_)))
        resolve(scope, base_, rest)

      // a[i, j := v] is a[i := a[i][j := v]] (see update)
      case Access(indices, Some(value)) :: rest =>
        val indices_ = indices.map(resolve(scope, _))
        val value_ = resolve(scope, value)
        val base_ = update(base, indices_, value_)
        resolve(scope, base_, rest)

      // the component i of the last value of a trace of several accumulators, current(S).i, and of its history, ⌊S⌋.i
      // (see core.Component)
      case Member(index) :: rest =>
        val base_ = base match
          case core.Current(trace) if several(trace) => core.Component(trace, index)
          case core.Butlast(trace) if several(trace) => core.History(trace, index)
          case _ => Error.raise("component of an expression that is not a trace of several accumulators", base, index)
        resolve(scope, base_, rest)

  // whether a trace has several accumulators, by its type
  def several(trace: core.Expr): Boolean =
    trace.typ match
      case core.Sort(core.Con.trace, List(elem)) => core.Trace.components(elem).length >= 2
      case _                                     => false

  // the guarded cases of a result, a single case with the guard true is the plain result
  def cases(scope: Scope, update: List[(Expr, Expr)]): core.Expr =
    update match
      case List((True, result)) =>
        resolve(scope, result)
      case _ =>
        core.Eps(update.map((guard, result) => core.Upd(resolve(scope, guard), resolve(scope, result))))

  // groups of variables with a common type, x, y: int, b: bool
  def flatten(groups: Typed): List[(String, Type)] =
    for
      (xs, typ) <- groups
      x <- xs
    yield (x, typ)

  def resolve(scope: Scope, expr: Expr): core.Expr =
    expr match
      case Dec(value) =>
        state.exprs.dec(util.Rational.decimal(value))

      case Num(value) =>
        state.exprs.num(BigInt(value))

      // backslashes escape the next character
      case Str(value) =>
        state.exprs.str(util.Strings.unescape(value))

      case App("!=", args) =>
        val expr_ = App("not", List(App("=", args)))
        resolve(scope, expr_)

      // the combinators of trace equation systems, whose bound variables are typed by the dependencies
      // the first bound variables of a trace are its accumulators, as many as it has initial values, with one result
      // each (as in Dafny)
      case Combinator("trace", inits, deps, ids, updates) =>
        Error.report("mismatching initial values and results of a trace", expr):
          require(inits.length == updates.length && ids.length > inits.length)
        val (accs, bound) = ids.splitAt(inits.length)
        val inits_ = inits.map(resolve(scope, _))
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.trace(inits_, deps_, accs.map(util.Name(_, None)), bound.map(util.Name(_, None))): (accs_, bound_) =>
          val scope_ = scope ++ (accs_ ++ bound_)
          updates.map(update => cases(scope_, update))

      case Combinator("map", Nil, deps, bound, List(update)) =>
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.map(deps_, bound.map(util.Name(_, None))): bound_ =>
          cases(scope ++ bound_, update)

      case Combinator("all", Nil, deps, bound, List(List((_, body)))) =>
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.all(deps_, bound.map(util.Name(_, None))): bound_ =>
          resolve(scope ++ bound_, body)

      // the value at the entry of the procedure
      case App("old", List(arg)) =>
        state.exprs.old(resolve(scope, arg))

      case App(name, Nil) if scope.vars.contains(name) =>
        scope.vars(name)

      case App(fun, args) if state.funs.contains((fun, args.length)) =>
        val args_ = args.map(resolve(scope, _))
        state.exprs.app(fun, args_)

      case Inner(base, access) =>
        val base_ = resolve(scope, base)
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
        val bound_ = flatten(bound).map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.ex(bound_, body_)

      case All(bound, triggers, body) =>
        val bound_ = flatten(bound).map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.all(bound_, body_)

      // a map of several indices, which are nested lambdas of a single variable (see core.Lams)
      case Lam(bound, body) =>
        val bound_ = flatten(bound).map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.lams(bound_, body_)

      case _ =>
        Error.raise("unknown expression", expr)

  def variables(scope: Scope, names: List[String]): List[core.Var] =
    val unknown = names.filterNot(scope.vars.contains(_))
    Error.report("unknown variables", unknown):
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

  // statements are resolved, the global variables that they modify are checked by Type.check
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
          yield update(x_, indices.flatten.map(resolve(scope, _)), resolve(scope, expr))

        state.progs.assign(lhs_, rhs_)

      case Havoc(names) =>
        val xs_ = variables(scope, names)
        state.progs.havoc(xs_)

      case Call(lhs, name, args) =>
        Error.report("procedure not declared", name):
          require(state.procs.contains(name))

        val lhs_ = variables(scope, lhs)
        val args_ = args.map(resolve(scope, _))
        state.progs.call(name, args_, lhs_)

      case Block(locals, progs) =>
        val locals_ = locals.flatMap(local => flatten(local.vars)).map(resolve(scope, _))
        val scope_ = scope ++ locals_
        val progs_ = progs.map(resolve(scope_, _))
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

      // loops without test are nondeterministic iterations
      case While(test, specs, body) =>
        val attrs_ = contract(scope, specs)
        val body_ = resolve(scope, body)

        test match
          case Some(test) =>
            val test_ = resolve(scope, test)
            state.progs.while_(test_, body_, attrs_)

          case None =>
            state.progs.iter(body_, attrs_)
