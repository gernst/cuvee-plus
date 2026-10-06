package cuvee.dafny

import util.Name
import cuvee.Error
import cuvee.core
import cuvee.core.State
import cuvee.core.Scope
import cuvee.core.types
import cuvee.core.Attrs

class Parser(var state: State):
  // val attrs_ = Attrs.empty

  // the constructors and selectors of a datatype whose sort is declared already
  def datatype(data: DataDef) =
    val DataDef(_, name, params, constrs, _) = data
    val scope = Scope.empty
    val params_ = params.map(resolve(scope, _))
    val scope_ = scope ++ params_
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
            state.funs(qname, 1)

        // the formal parameters of constructors are named after the selectors
        val formals_ =
          for sel_ <- sels_
          yield state.exprs.formal(sel_.name, sel_.res)

        state = state.declare(constr, params_, formals_, sort_, Attrs.empty)
        (state.funs((constr, formals_.length)), sels_)

    state = state.define(name, core.Datatype(params_, constrs_))

  // the strongly connected components of the datatypes `names` by the sorts of their selectors,
  // each after those that it refers to, and otherwise in the given order
  def groups(names: List[Name]): List[List[Name]] =
    val refs =
      names.map: name =>
        val core.Datatype(_, constrs) = state.datatypes(name)
        val cons = constrs.flatMap(_._2).flatMap(_.res.cons).map(_.name).toSet
        name -> names.filter(cons.contains).toSet
      .toMap

    // the datatypes reachable from each one
    def reach(todo: List[Name], seen: Set[Name]): Set[Name] =
      todo match
        case Nil                         => seen
        case n :: rest if seen contains n => reach(rest, seen)
        case n :: rest                   => reach(refs(n).toList ++ rest, seen + n)

    val reachable = names.map(n => n -> reach(refs(n).toList, Set())).toMap
    val components = names.map(n => names.filter(m => m == n || reachable(n)(m) && reachable(m)(n))).distinct

    def order(todo: List[List[Name]], done: List[List[Name]]): List[List[Name]] =
      todo match
        case Nil => done
        case _ =>
          val emitted = done.flatten.toSet
          val next = todo.find(c => c.forall(n => (reachable(n) -- c).subsetOf(emitted))).get
          order(todo.filterNot(_ == next), done :+ next)

    order(components, Nil)

  // type checking resolves the overloaded operators, see core.Overload
  def check(scope: Scope, expr: core.Expr, typ: core.Type): core.Expr =
    state.exprs.check(scope, expr, typ)

  def check(scope: Scope, fixed: Set[core.Var], mod: Set[core.Var], prog: core.Prog): core.Prog =
    state.progs.check(scope, fixed, mod, prog)

  def resolve(scope: Scope, name: String): core.Param =
    state.types.param(name)

  def resolve(scope: Scope, formal: (String, Type)): core.Var =
    val (name, typ) = formal
    state.exprs.formal(name, resolve(scope, typ))

  def resolve(cmd: Cmd): List[core.Cmd] =
    cmd match
      case Check =>
        List(core.CheckSat)

      case VarDef(vars) =>
        val scope = Scope.empty
        for (name, typ) <- vars
        yield
          val typ_ = resolve(scope, typ)
          state = state.declare(name, typ_, Attrs.empty)
          state.cmds.declareVar(name)

      case Axiom(params, attrs, expr) =>
        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        List(state.cmds.axiom(params_, phi_, attrs_))

      case Lemma(params, attrs, expr) =>
        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        List(state.cmds.lemma(params_, phi_, attrs_))

      case Goal(params, attrs, expr) =>
        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        List(state.cmds.goal(params_, phi_, attrs_))

      case SortDef(attrs, name, params, impl) =>
        val scope = Scope.empty
        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val arity_ = params.length
        state = state.declare(name, arity_, Attrs(attrs.map(_ -> None)))

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

      // the sorts of consecutive datatypes are declared first, such that the constructors may refer to all of them,
      // then each group of mutually recursive datatypes is declared together, those that it refers to first,
      // followed by the members of all of them
      case DataDefs(datas) =>
        for DataDef(attrs, name, params, _, _) <- datas
        do state = state.declare(name, params.length, Attrs(attrs.map(_ -> None)))

        for data <- datas
        do datatype(data)

        val names = datas.map(data => Name(data.name, None))
        val decls = groups(names).map(state.cmds.declareDatatypes)

        val members =
          for
            DataDef(_, name, params, _, impl) <- datas
            cmds <- impl.toList
            params_ = params.map(resolve(Scope.empty, _))
            this_ = state.exprs.formal("this", state.types.sort(name, params_))
            cmd <- cmds
            cmd_ <- resolve(Scope.empty ++ params_, name + "_", params_, List(this_), cmd)
          yield cmd_

        decls ++ members

      case _ =>
        resolve(Scope.empty, "", Nil, Nil, cmd)

  // the formula of an axiom, lemma, or goal is resolved and checked in the scope of its type parameters,
  // the type parameters of the assertion are these followed by those that remain in the formula otherwise
  def assertion(params: List[String], attrs: List[String], expr: Expr): (List[core.Param], core.Expr, Attrs) =
    val params_ = params.map(resolve(Scope.empty, _))
    val phi_ = formula(Scope.empty ++ params_, expr)
    val attrs_ = Attrs(attrs.map(_ -> None))
    (params_ ++ phi_.params.toList.filterNot(params_.contains), phi_, attrs_)

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

  // the modifies clause, invariants, and termination measure of a loop
  def loop(scope: Scope, mod: List[List[String]], invs: List[Expr], dec: List[List[Expr]]) =
    Attrs(contract(scope, mod, Nil, Nil, Nil).attrs ++ invariants(scope, invs, dec).attrs)

  // the components of a lexicographic termination measure in order, each of which is an integer
  def decreases(scope: Scope, dec: List[List[Expr]]) =
    for expr <- dec.flatten
    yield "decreases" -> Some(measure(scope, expr))

  def resolve(scope: Scope, prefix: String, outer_ : List[core.Param], self: List[core.Var], cmd: Cmd): List[core.Cmd] =
    cmd match
      case FunDef(attrs, fun, inner, formals, typ, req, ens, dec, body) =>
        val qname = prefix + fun

        val inner_ = inner.map(resolve(scope, _))
        val params_ = outer_ ++ inner_
        val scope_ = scope ++ inner_

        val formals_ = self ++ formals.map(resolve(scope_, _))

        val typ_ = resolve(scope_, typ)
        val scope__ = scope_ ++ formals_
        val attrs_ = Attrs(attrs.map(_ -> None) ++ contract(scope__, Nil, req, ens, dec).attrs)

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

      case MethodDef(meth, inner, formals, rets, mod, req, ens, assumes, commits, dec, body) =>
        val qname = prefix + meth

        val inner_ = inner.map(resolve(scope, _))
        val params_ = outer_ ++ inner_
        val scope_ = scope ++ inner_

        val formals_ = self ++ formals.map(resolve(scope_, _))
        val rets_ = rets.toList.flatten.map(resolve(scope_, _))

        // methods may read all global variables and modify those in their modifies clause,
        // the formal parameters shadow global variables of the same name
        val globals = state.globals
        val scope__ = scope_ ++ globals ++ formals_ ++ rets_
        val ac_ =
          assumes.map(phi => "assumes" -> Some(formula(scope__, phi))) ++
            commits.map(phi => "commits" -> Some(formula(scope__, phi)))
        val attrs_ = Attrs(contract(scope__, mod, req, ens, dec).attrs ++ ac_)
        state = state.declare(qname, params_, formals_, rets_, attrs_)

        val mod_ = attrs_.modifies
        val nonglobal = mod_.filterNot(globals.contains)
        Error.report("modifies clause of method lists variables that are not global", qname, nonglobal):
          require(nonglobal.isEmpty)

        body match
          case None =>
            val cmd_ = state.cmds.declareProc(qname)
            List(cmd_)

          // the inputs of a method and the global variables that are not modified must not be assigned
          case Some(prog) =>
            val prog_ = resolve(scope__, prog)
            val fixed = formals_.toSet ++ (globals.toSet -- mod_)
            val body_ = check(scope__, fixed, mod_.toSet, prog_)
            state = state.define(qname, body_)

            val cmd_ = state.cmds.defineProc(qname)
            List(cmd_)

      case _ =>
        Error.raise("unsupported nested command", prefix, cmd)

  def resolve(scope: Scope, typ: Type): core.Type =
    typ match
      // the tuple types are declared in the prelude
      case Product(args) =>
        val args_ = args.map(resolve(scope, _))
        state.types.sort("tuple" + args.length, args_)

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

      // arrays and sequences, resolved by overloading (see core.Overload)
      case Array(index, None) :: rest =>
        val index_ = resolve(scope, index)
        val base_ = state.exprs.app("select", List(base, index_))
        resolve(scope, base_, rest)

      case Array(index, Some(value)) :: rest =>
        val index_ = resolve(scope, index)
        val value_ = resolve(scope, value)
        val base_ = state.exprs.app("store", List(base, index_, value_))
        resolve(scope, base_, rest)

      // s[i..j] is the subsequence of length j - i from offset i, the bounds default to 0 and |s|
      case Slice(from, to) :: rest =>
        val from_ = from.map(resolve(scope, _)).getOrElse(state.exprs.num(0))
        val to_ = to.map(resolve(scope, _)).getOrElse(state.exprs.app(core.Fun.seq.len, List(base)))
        val len_ = from match
          case None    => to_
          case Some(_) => state.exprs.app("-", List(to_, from_))
        val base_ = state.exprs.app(core.Fun.seq.extract, List(base, from_, len_))
        resolve(scope, base_, rest)

      // the keys and values m.Keys and m.Values of maps, which are sets
      case Member("Keys", Nil) :: rest if isMap(base) =>
        resolve(scope, state.exprs.app(core.Fun.map.keys, List(base)), rest)

      case Member("Values", Nil) :: rest if isMap(base) =>
        resolve(scope, state.exprs.app(core.Fun.map.values, List(base)), rest)

      // testers x.C? of the constructors of datatypes, on variables only like members
      case Member(tester, Nil) :: rest if tester.endsWith("?") && state.constrs.contains(tester.dropRight(1)) =>
        Error.report("tester on an expression that is not a variable", base, tester):
          require(base.isInstanceOf[core.Var])

        val base_ = state.exprs.is(base, tester.dropRight(1))
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

  def isMap(expr: core.Expr): Boolean =
    expr.typ match
      case core.Sort(con, _) => con == core.Con.map
      case _                 => false

  def resolve(scope: Scope, expr: Expr): core.Expr =
    expr match
      case Num(value) =>
        state.exprs.num(BigInt(value))

      case Dec(value) =>
        state.exprs.dec(util.Rational.decimal(value))

      // backslashes escape the next character
      case Str(value) =>
        state.exprs.str(util.Strings.unescape(value))

      case Tuple(List(arg)) =>
        resolve(scope, arg)

      // the constructors of tuples are declared in the prelude
      case Tuple(args) =>
        val args_ = args.map(resolve(scope, _))
        state.exprs.app("tuple" + args.length, args_)

      // [a, b, c] is the concatenation of the sequences of length 1, [a] + [b] + [c]
      case SeqLit(Nil) =>
        state.exprs.app(core.Fun.seq.empty, Nil)

      case SeqLit(args) =>
        val units_ =
          for arg <- args
          yield state.exprs.app(core.Fun.seq.unit, List(resolve(scope, arg)))
        units_.reduceLeft((left, right) => state.exprs.app(core.Fun.seq.concat, List(left, right)))

      // the length of a sequence, or the cardinality of a set or multiset, resolved by overloading (see core.Overload)
      case Len(arg) =>
        val arg_ = resolve(scope, arg)
        state.exprs.app(core.Overload.card, List(arg_))

      // {a, b, c} is the union of the singletons, multiset{a, b, c} that of the elements with multiplicity 1
      case SetLit(Nil) =>
        state.exprs.app(core.Fun.set.empty, Nil)

      case SetLit(args) =>
        val singletons_ =
          for arg <- args
          yield state.exprs.app(core.Fun.set.singleton, List(resolve(scope, arg)))
        singletons_.reduceLeft((left, right) => state.exprs.app(core.Fun.set.union, List(left, right)))

      case BagLit(Nil) =>
        state.exprs.app(core.Fun.bag.empty, Nil)

      case BagLit(args) =>
        val elems_ =
          for arg <- args
          yield state.exprs.app(core.Fun.bag.make, List(resolve(scope, arg), state.exprs.num(1)))
        elems_.reduceLeft((left, right) => state.exprs.app(core.Fun.bag.union, List(left, right)))

      // map[k := v, ...] overwrites the singleton maps from left to right, such that later keys win, as in Dafny
      case MapLit(Nil) =>
        state.exprs.app(core.Fun.map.empty, Nil)

      case MapLit(args) =>
        val singletons_ =
          for (key, value) <- args
          yield state.exprs.app(core.Fun.map.singleton, List(resolve(scope, key), resolve(scope, value)))
        singletons_.reduceLeft((left, right) => state.exprs.app(core.Fun.map.update, List(left, right)))

      // chained comparisons x < y <= z are the conjunction x < y && y <= z, which must not mix directions, as in Dafny
      case Chain(ops, args) =>
        Error.report("chained comparisons in different directions", ops):
          require(!(ops.exists(Set("<", "<=")) && ops.exists(Set(">", ">="))))

        val pairs =
          for ((op, left), right) <- ops zip args zip args.tail
          yield App(op, List(left, right), Nil)
        resolve(scope, pairs.reduceLeft((phi, psi) => App("and", List(phi, psi), Nil)))

      case Butlast(arg) =>
        val arg_ = resolve(scope, arg)
        state.exprs.app(core.Fun.trace.butlast, List(arg_))

      // membership in sequences, sets, and multisets, resolved by overloading (see core.Overload)
      case App("in", List(elem, coll), Nil) =>
        val elem_ = resolve(scope, elem)
        val coll_ = resolve(scope, coll)
        state.exprs.app(core.Overload.member, List(elem_, coll_))

      case App("!in", args, Nil) =>
        val expr_ = App("not", List(App("in", args, Nil)), Nil)
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

      // the value at the entry of the method
      case App("old", List(arg), Nil) =>
        state.exprs.old(resolve(scope, arg))

      // unary + is the identity
      case App("+", List(arg), Nil) =>
        resolve(scope, arg)

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

      case Access_(base, access) =>
        val base_ = resolve(scope, base)
        resolve(scope, base_, access)

      case As(arg, typ) =>
        val arg_ = resolve(scope, arg)
        val typ_ = resolve(scope, typ)
        state.exprs.as(arg_, typ_)

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

      case While(Some(test), mod, invs, dec, body) =>
        val test_ = resolve(scope, test)
        val body_ = resolve(scope, body)
        val attrs_ = loop(scope, mod, invs, dec)
        state.progs.while_(test_, body_, attrs_)

      case While(None, mod, invs, dec, body) =>
        val body_ = resolve(scope, body)
        val attrs_ = loop(scope, mod, invs, dec)
        state.progs.iter(body_, attrs_)

      case Par(calls) =>
        val calls_ =
          for call <- calls
          yield resolve(scope, call) match
            case call_ : core.Call => call_
            case prog_             => Error.raise("parallel composition of statements that are not calls", prog_)
        state.progs.par(calls_)

      // the evolution constraint defaults to true
      // the time is bound on real in the right hand sides, the evolution constraint, and the invariants
      case Ode(time, xs, rhs, dom, invs) =>
        val unknown = xs.filterNot(scope.vars.contains(_))
        Error.report("unknown local variables", scope, unknown, xs):
          require(unknown.isEmpty)

        val time_ = core.Var(time, core.Sort.real)
        val scope_ = scope ++ List(time_)
        val xs_ = xs.map(scope.vars(_))
        val rhs_ = rhs.map(resolve(scope_, _))
        val dom_ = dom.map(resolve(scope_, _)).getOrElse(core.True)
        val attrs_ = invariants(scope_, invs, Nil)
        state.progs.ode(time_, xs_, rhs_, dom_, attrs_)
