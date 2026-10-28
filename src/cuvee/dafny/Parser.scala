package cuvee.dafny

import util.Name
import cuvee.Error
import cuvee.core
import cuvee.core.State
import cuvee.core.Scope
import cuvee.core.types
import cuvee.core.Attrs
import cuvee.sexpr

class Parser(var state: State):
  // the commands of an included file, parsed by a fresh parser (see Source.included)
  var include: String => List[core.Cmd] =
    path => Error.raise("include not supported here", path)

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

        // the formal parameters of constructors are numbered as in SMT-LIB, such that they coincide with the
        // built-in constructors (see core.Fun)
        val formals_ = core.Expr.vars("x", sels_.map(_.res))

        state = state.declare(constr, params_, formals_, sort_, Attrs.empty)
        (state.funs((constr, formals_.length)), sels_)

    state = state.define(name, core.Datatype(params_, constrs_))

  // the strongly connected components of the datatypes `names` by the sorts of their selectors,
  // each after those that it refers to, and otherwise in the given order
  def groups(names: List[Name]): List[List[Name]] =
    util.SCC(names, name =>
      val core.Datatype(_, constrs) = state.datatypes(name)
      constrs.flatMap(_._2).flatMap(_.res.cons).map(_.name).toSet)

  // the variables `names` in scope, unknown ones are reported with `msg`
  def vars(scope: Scope, names: List[String], msg: String): List[core.Var] =
    val unknown = names.filterNot(scope.vars.contains(_))
    Error.report(msg, unknown):
      require(unknown.isEmpty)
    names.map(scope.vars(_))

  // the variables that receive the results of a call, which are not updated at indices
  def results(scope: Scope, lhs: List[Lhs]): List[core.Var] =
    Error.report("results of calls must be assigned to variables", lhs):
      require(lhs.forall(_.indices.isEmpty))
    vars(scope, lhs.map(_.name), "unknown local variables")

  // the update of `base` at `indices` by `value`, a[i][j] := v is a := a[i := a[i][j := v]],
  // resolved by overloading for arrays, sequences, and maps
  def update(base: core.Expr, indices: List[core.Expr], value: core.Expr): core.Expr =
    indices match
      case Nil =>
        value

      case index :: rest =>
        val inner = state.exprs.app("select", List(base, index))
        val value_ = update(inner, rest, value)
        state.exprs.app("store", List(base, index, value_))

  // the assignment of `rhs` to the variables `lhs` or their elements, which are updated (see update)
  def assign(scope: Scope, lhs: List[Lhs], rhs: List[core.Expr]): core.Prog =
    Error.report("mismatching assignment", lhs, rhs):
      require(lhs.length == rhs.length)

    val lhs_ = vars(scope, lhs.map(_.name), "unknown local variables")
    val rhs_ =
      for (Lhs(_, indices), (x_, expr_)) <- lhs zip (lhs_ zip rhs)
      yield update(x_, indices.map(resolve(scope, _)), expr_)
    state.progs.assign(lhs_, rhs_)

  // the application of a function value by the application function of the prelude for the number of arguments
  // (see core.Apply), whose type is resolved by type checking
  def apply(scope: Scope, f: core.Expr, args: List[Expr]): core.Expr =
    Error.report("application of a value that is not a function", f):
      require(core.Arrow.unapply(f.typ).isDefined)
    state.exprs.app(Name("apply", Some(args.length)), f :: args.map(resolve(scope, _)))

  // the qualified name of member `fun` of the type of `self`, e.g. pair_fst, as declared with the name of the type
  // written with its subscripts, e.g. tuple₂_0
  def member(self: core.Var, fun: String) =
    self.typ.name.subscripted + "_" + fun

  // whether `fun` with `arity` arguments is a function or method of the type of `this` in scope,
  // i.e., inside the members of a type
  def isMember(scope: Scope, fun: String, arity: Int) =
    scope.vars.get("this").exists: self =>
      declared(member(self, fun), 1 + arity)

  // the qualified name of the static member `fun` with `arity` arguments of the type of `this` in scope, if any
  def static(scope: Scope, fun: String, arity: Int): Option[String] =
    scope.vars.get("this").map(member(_, fun)).filter(declared(_, arity))

  // whether `qname` is a function or method with `arity` inputs
  def declared(qname: String, arity: Int) =
    state.funs.contains((qname, arity)) || state.procs.get(qname).exists(_.in.length == arity)

  // the type parameters of a type among `params` that the types of a signature mention, all of them for members with
  // `this`
  def used(params: List[core.Param], types: List[core.Type]): List[core.Param] =
    params.filter(param => types.exists(_.params.contains(param)))

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

      // the declarations of the included file are known to the rest of the input
      case Include(path) =>
        val cmds = include(path)
        for case decl: core.Decl <- cmds do state = state.add(decl)
        cmds

      case VarDef(attrs, vars) =>
        val scope = Scope.empty
        for (name, typ) <- vars
        yield
          val typ_ = resolve(scope, typ)
          state = state.declare(name, typ_, keywords(attrs))
          state.cmds.declareVar(name)

      case Axiom(params, attrs, expr) =>
        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        List(state.cmds.axiom(params_, phi_, attrs_))

      // lemma name<a>(xs) returns (ys) requires φ ensures ψ is the assertion forall xs :: φ ==> exists ys :: ψ,
      // with its name as the attribute :named; a lemma without a body is free, one with the empty body needs a proof,
      // other bodies are not supported yet
      case Lemma(attrs, name, params, formals, rets, req, ens, body) =>
        Error.report("only lemmas without a body or with the empty body are supported", name):
          require(body.forall(_ == Block(Nil, Nil)))

        val post = Ex(rets.getOrElse(Nil), ens.reduceOption((phi, psi) => App("and", List(phi, psi))).getOrElse(True))
        val expr =
          req.reduceOption((phi, psi) => App("and", List(phi, psi))) match
            case None      => All(formals, post)
            case Some(pre) => All(formals, App("=>", List(pre, post)))

        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        val free = if body.isEmpty && !attrs.exists(_._1 == "free") then List("free" -> None) else Nil
        List(state.cmds.lemma(params_, phi_, Attrs(attrs_.attrs ++ free :+ ("named" -> Some(sexpr.Id(name))))))

      case Goal(params, attrs, expr) =>
        val (params_, phi_, attrs_) = assertion(params, attrs, expr)
        List(state.cmds.goal(params_, phi_, attrs_))

      // the variables of the composition g(f(xs), ys) are typed by the formal parameters of g and f,
      // whose type parameters are in scope; terms are accesses without selectors here
      case Fuse(attrs, term @ Inner(App(g, Inner(App(f, args), Nil) :: rest), Nil)) =>
        val names = (args ++ rest).collect { case Inner(App(name, Nil), Nil) => name }
        Error.report("fuse needs variables as the arguments", term):
          require(names.length == args.length + rest.length)
        Error.report("unknown functions", g, f):
          require(state.funs.contains((g, 1 + rest.length)) && state.funs.contains((f, args.length)))

        val gf = state.funs((g, 1 + rest.length))
        val ff = state.funs((f, args.length))
        val xs = (names zip (ff.args ++ gf.args.tail)).map(state.exprs.formal(_, _))
        val scope = Scope((ff.params ++ gf.params).distinct, xs)
        val term_ = check(scope, resolve(scope, term), gf.res)
        List(core.FuseFuns(term_, None, keywords(attrs)))

      case Fuse(_, term) =>
        Error.raise("fuse needs a composition g(f(x₁, ..., xₙ), y₁, ..., yₘ) of two defined functions", term)

      case SortDef(attrs, name, params, impl) =>
        val scope = Scope.empty
        val params_ = params.map(resolve(scope, _))
        val scope_ = scope ++ params_

        val arity_ = params.length
        state = state.declare(name, arity_, keywords(attrs))

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
        do state = state.declare(name, params.length, keywords(attrs))

        for data <- datas
        do datatype(data)

        // names with subscripts are indexed, e.g. tuple₂
        val names = datas.map(data => data.name: Name)
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
  def assertion(params: List[String], attrs: List[Annotation], expr: Expr): (List[core.Param], core.Expr, Attrs) =
    val params_ = params.map(resolve(Scope.empty, _))
    val phi_ = formula(Scope.empty ++ params_, expr)
    val attrs_ = keywords(attrs)
    (params_ ++ phi_.params.toList.filterNot(params_.contains), phi_, attrs_)

  // annotations without values, e.g. {:rw}
  def keywords(attrs: List[Annotation]): Attrs =
    for (name, arg) <- attrs
    do
      Error.report("annotation with a value", name):
        require(arg.isEmpty)

    Attrs(attrs.map((name, _) => name -> None))

  // the annotations of an implementation `fun`, a function or a method, whose inputs are in `scope`, where
  // {:implement pattern} names the function that it implements and the positions of its arguments by an application
  // to the inputs, of the type `res` of the result of the function or of the single output of the method (see
  // transform.Implement and transform.Choose); other annotations have no values
  def annotations(fun: String, scope: Scope, attrs: List[Annotation], res: core.Type): Attrs =
    val attrs_ =
      for (name, arg) <- attrs
      yield arg match
        case Some(pattern) if name == "implement" =>
          val pattern_ = resolve(scope, pattern)
          Error.report("the pattern of {:implement} does not have the result type of the implementation", fun):
            name -> Some(check(scope, pattern_, res))

        // the input of an implementing method that receives the context of the client (see transform.Implement)
        case Some(input) if name == "context" =>
          name -> Some(resolve(scope, input))

        case Some(_) =>
          Error.raise("annotation with a value", name)

        case None =>
          name -> None

    Attrs(attrs_)

  def formula(scope: Scope, phi: Expr) =
    val expr_ = resolve(scope, phi)
    val typ_ = state.types.sort("Bool")
    check(scope, expr_, typ_)

  def measure(scope: Scope, expr: Expr) =
    val expr_ = resolve(scope, expr)
    val typ_ = state.types.sort("Int")
    check(scope, expr_, typ_)

  def contract(scope: Scope, mod: List[List[String]], req: List[Expr], ens: List[Expr], dec: List[List[Expr]]) =
    val mod_ =
      for xs <- mod
      yield "modifies" -> Some(vars(scope, xs, "unknown variables in modifies clause"))

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
      // static members have no `this`, hence only those type parameters of the type that their signature mentions
      // (see used), e.g. the parameter b of a datatype map<a, b> for static predicate R(c: int, v: b), such that
      // their instances are determined by the arguments and the result
      case Static(cmd) =>
        resolve(scope, prefix, outer_, Nil, cmd)

      case FunDef(attrs, fun, inner, formals, typ, req, ens, dec, body) =>
        val qname = prefix + fun

        val inner_ = inner.map(resolve(scope, _))
        val scope_ = scope ++ inner_

        val formals_ = self ++ formals.map(resolve(scope_, _))

        val typ_ = resolve(scope_, typ)
        val params_ = used(outer_, typ_ :: formals_.types) ++ inner_
        val scope__ = scope_ ++ formals_
        val attrs_ = annotations(qname, scope__, attrs, typ_) ++ contract(scope__, Nil, req, ens, dec)

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

      case MethodDef(attrs, meth, inner, formals, rets, mod, req, ens, assumes, commits, dec, body) =>
        val qname = prefix + meth

        val inner_ = inner.map(resolve(scope, _))
        val scope_ = scope ++ inner_

        val formals_ = self ++ formals.map(resolve(scope_, _))
        val rets_ = rets.toList.flatten.map(resolve(scope_, _))
        val params_ = used(outer_, formals_.types ++ rets_.types) ++ inner_

        // methods may read all global variables and modify those in their modifies clause,
        // the formal parameters shadow global variables of the same name
        val globals = state.globals
        val scope__ = scope_ ++ globals ++ formals_ ++ rets_
        val ac_ =
          assumes.map(phi => "assumes" -> Some(formula(scope__, phi))) ++
            commits.map(phi => "commits" -> Some(formula(scope__, phi)))
        // a method that implements a function by {:implement pattern} has a single output, the result
        val annots_ =
          if attrs.exists((name, arg) => name == "implement" && arg.nonEmpty)
          then
            Error.report("a method with {:implement pattern} has a single output", qname):
              require(rets_.length == 1)
            annotations(qname, scope_ ++ formals_, attrs, rets_.head.typ)
          else keywords(attrs)

        val attrs_ = Attrs(annots_.attrs ++ contract(scope__, mod, req, ens, dec).attrs ++ ac_)
        state = state.declare(qname, params_, formals_, rets_, attrs_)

        val mod_ = attrs_.modifies
        state.progs.modifies(qname, mod_)

        body match
          case None =>
            val cmd_ = state.cmds.declareProc(qname)
            List(cmd_)

          case Some(prog) =>
            val prog_ = resolve(scope__, prog)
            val body_ = state.progs.body(scope__, formals_, mod_, prog_)
            state = state.define(qname, body_)

            val cmd_ = state.cmds.defineProc(qname)
            List(cmd_)

      case _ =>
        Error.raise("unsupported nested command", prefix, cmd)

  def resolve(scope: Scope, typ: Type): core.Type =
    typ match
      case Product(List(typ)) =>
        resolve(scope, typ)

      // the tuple types are declared in the prelude
      case Product(args) =>
        val args_ = args.map(resolve(scope, _))
        state.types.sort(Name("tuple", Some(args.length)), args_)

      // the function types are declared in the prelude, (A, B) -> C has two arguments, ((A, B)) -> C a tuple
      case Arrow(arg, res) =>
        val args = arg match
          case Product(args) => args
          case _             => List(arg)
        val args_ = args.map(resolve(scope, _))
        val res_ = resolve(scope, res)
        state.types.sort(Name("arrow", Some(args.length)), args_ :+ res_)

      case Sort(name, Nil) if scope.params.contains(name) =>
        scope.params(name)

      // bitvectors bv1, bv2, ..., unless the name is declared otherwise
      case Sort(name, Nil) if name.matches("bv[1-9][0-9]*") && !state.sorts.contains(name) =>
        core.BitVec(name.drop(2).toInt)

      case Sort(name, args) if state.sorts.contains(name) =>
        val args_ = args.map(resolve(scope, _))
        state.types.sort(name, args_)

      case _ =>
        Error.raise("unknown type", typ)

  // members are looked up by the name of the type of `base`, which is resolved here,
  // since the type of an application may still be a fresh type parameter
  // fields of datatypes are their selectors, which are declared without the datatype as prefix
  def resolve(scope: Scope, base: core.Expr, access: List[Access]): core.Expr =
    access match
      case Nil =>
        base

      // arrays and sequences, resolved by overloading (see core.Overload)
      case Array(Some(index), None) :: rest =>
        val index_ = resolve(scope, index)
        val base_ = state.exprs.app("select", List(base, index_))
        resolve(scope, base_, rest)

      case Array(Some(index), Some(Store(value))) :: rest =>
        val index_ = resolve(scope, index)
        val value_ = resolve(scope, value)
        val base_ = state.exprs.app("store", List(base, index_, value_))
        resolve(scope, base_, rest)

      // s[i..j] is the subsequence of length j - i from offset i, the bounds default to 0 and |s|
      case Array(from, Some(Upto(to))) :: rest =>
        val from_ = from.map(resolve(scope, _)).getOrElse(state.exprs.num(0))
        val to_ = to.map(resolve(scope, _)).getOrElse(state.exprs.app(core.Fun.seq.len, List(base)))
        val len_ = from match
          case None    => to_
          case Some(_) => state.exprs.app("-", List(to_, from_))
        val base_ = state.exprs.app(core.Fun.seq.extract, List(base, from_, len_))
        resolve(scope, base_, rest)

      case Array(None, _) :: _ =>
        Error.raise("missing index", base)

      // conversions to integers and bitvectors, whose implementation depends on the type of the base,
      // which is determined by type checking (see Overload.conversion), other targets are type annotations
      case As(typ) :: rest =>
        val typ_ = resolve(scope, typ)
        val base_ = typ_ match
          case core.Sort.int  => state.exprs.app(core.Overload.toInt, List(base))
          case core.BitVec(_) => state.exprs.app(core.Overload.toBitVec, List(base)).copy(typ = typ_)
          case _              => state.exprs.as(base, typ_)
        resolve(scope, base_, rest)

      // the keys and values m.Keys and m.Values of maps, which are sets, other types are rejected by type checking
      case Member("Keys", Nil) :: rest =>
        resolve(scope, state.exprs.app(core.Fun.map.keys, List(base)), rest)

      case Member("Values", Nil) :: rest =>
        resolve(scope, state.exprs.app(core.Fun.map.values, List(base)), rest)

      // testers x.C? of the constructors of datatypes, on variables only like members,
      // where state.exprs.is rejects unknown constructors
      case Member(tester, Nil) :: rest if tester.endsWith("?") =>
        Error.report("tester on an expression that is not a variable", base, tester):
          require(base.isInstanceOf[core.Var])

        val base_ = state.exprs.is(base, tester.dropRight(1))
        resolve(scope, base_, rest)

      // the component i of the last value of a trace of several accumulators, current(S).i, and of its history, ⌊S⌋.i,
      // where the type of S is known from its declaration (see core.Component)
      case Member(index, Nil) :: rest if index.forall(_.isDigit) && component(base).isDefined =>
        val Some((trace, history)) = component(base): @unchecked
        val base_ = if history then core.History(trace, index.toInt) else core.Component(trace, index.toInt)
        resolve(scope, base_, rest)

      // members are accessed on variables only, whose type is known without type checking
      case Member(fun, args) :: rest =>
        val self = base match
          case self: core.Var => self
          case _              => Error.raise("member access on an expression that is not a variable", base, fun)

        val qname = member(self, fun)

        args match
          case _ if state.funs.contains((qname, 1 + args.length)) =>
            val args_ = args.map(resolve(scope, _))
            val base_ = state.exprs.app(qname, self :: args_)
            resolve(scope, base_, rest)

          case _ if state.procs.contains(qname) =>
            Error.raise("method call not allowed here", self, qname, args)

          case _ =>
            Error.raise("invalid access", self, qname, access)

  // the trace of current(S) or butlast(S) if its type has several components, and whether it is the history
  def component(base: core.Expr): Option[(core.Expr, Boolean)] =
    def several(trace: core.Expr) =
      trace.typ match
        case core.Sort(core.Con.trace, List(elem)) => core.Trace.components(elem).length >= 2
        case _                                     => false
    base match
      case core.Current(trace) if several(trace) => Some((trace, false))
      case core.Butlast(trace) if several(trace) => Some((trace, true))
      case _                                     => None

  // the guarded cases of a result, a single case with the guard true is the plain result
  def update(scope: Scope, update: List[(Expr, Expr)]): core.Expr =
    update match
      case List((True, result)) =>
        resolve(scope, result)
      case _ =>
        core.Eps(update.map((guard, result) => core.Upd(resolve(scope, guard), resolve(scope, result))))

  // the comparisons that can be chained, with the translated operators
  val chainable = Grammar.chainable.map(op => Grammar.translate.getOrElse(op, op))

  // the operators and operands of a chain, which associates to the left
  def chain(expr: Expr): (List[String], List[Expr]) =
    expr match
      case App(op, List(left, right)) if chainable(op) =>
        val (ops, args) = chain(left)
        (ops :+ op, args :+ right)

      case _ =>
        (Nil, List(expr))

  def resolve(scope: Scope, expr: Expr): core.Expr =
    expr match
      // numeric literals are integers or bitvectors, depending on the context, and integers by default (see Type.instantiate)
      case Num(value) =>
        core.Lit(BigInt(value), core.Param("n").fresh)

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
        state.exprs.app(Name("tuple", Some(args.length)), args_)

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

      // {a, b, c} inserts b and c into the singleton {a}, s[b := true], pointwise rather than unions of singletons,
      // e.g. for the encoding of renc; multiset{a, b, c} is the union of the elements with multiplicity 1
      case SetLit(Nil) =>
        state.exprs.app(core.Fun.set.empty, Nil)

      case SetLit(first :: rest) =>
        val singleton_ : core.Expr = state.exprs.app(core.Fun.set.singleton, List(resolve(scope, first)))
        rest.foldLeft(singleton_):
          case (set_, elem) =>
            state.exprs.app(core.Fun.set.update, List(set_, resolve(scope, elem), state.exprs.app(core.Fun.true_, Nil)))

      case BagLit(Nil) =>
        state.exprs.app(core.Fun.bag.empty, Nil)

      case BagLit(args) =>
        val elems_ =
          for arg <- args
          yield state.exprs.app(core.Fun.bag.make, List(resolve(scope, arg), state.exprs.num(1)))
        elems_.reduceLeft((left, right) => state.exprs.app(core.Fun.bag.union, List(left, right)))

      // map[k := v, ...] stores the further pairs into the singleton of the first from left to right, such that later
      // keys win, as in Dafny; stores rather than merges of singletons, which are pointwise, e.g. for the encoding of
      // renc
      case MapLit(Nil) =>
        state.exprs.app(core.Fun.map.empty, Nil)

      case MapLit((key, value) :: rest) =>
        val singleton_ : core.Expr = state.exprs.app(core.Fun.map.singleton, List(resolve(scope, key), resolve(scope, value)))
        rest.foldLeft(singleton_):
          case (map_, (key, value)) =>
            state.exprs.app(core.Fun.map.store, List(map_, resolve(scope, key), resolve(scope, value)))

      // chained comparisons x < y <= z are the conjunction x < y && y <= z, which must not mix directions, as in Dafny;
      // parenthesized comparisons are tuples, which do not chain, e.g. (x == y) == b
      case App(op, List(App(op_, List(_, _)), _)) if chainable(op) && chainable(op_) =>
        val (ops, args) = chain(expr)
        Error.report("chained comparisons in different directions", ops):
          require(!(ops.exists(Set("<", "<=")) && ops.exists(Set(">", ">="))))

        val pairs =
          for ((op, left), right) <- ops zip args zip args.tail
          yield App(op, List(left, right))
        resolve(scope, pairs.reduceLeft((phi, psi) => App("and", List(phi, psi))))

      case Butlast(arg) =>
        val arg_ = resolve(scope, arg)
        state.exprs.app(core.Fun.trace.butlast, List(arg_))

      // membership in sequences, sets, and multisets, resolved by overloading (see core.Overload)
      case App("in", List(elem, coll)) =>
        val elem_ = resolve(scope, elem)
        val coll_ = resolve(scope, coll)
        state.exprs.app(core.Overload.member, List(elem_, coll_))

      case App("!in", args) =>
        val expr_ = App("not", List(App("in", args)))
        resolve(scope, expr_)

      // the combinators of trace equation systems, whose bound variables are typed by the dependencies; the first
      // bound variables of a trace are its accumulators, as many as it has initial values, with one result each;
      // the names are converted like those of other binders, such that a subscript is an index, e.g. x₀
      case Combinator("trace", inits, deps, ids, updates) =>
        Error.report("trace without initial value", expr):
          require(inits.nonEmpty)
        Error.report("mismatching initial values and results of a trace", expr):
          require(inits.length == updates.length && ids.length > inits.length)
        val (accs, bound) = ids.splitAt(inits.length)
        val inits_ = inits.map(resolve(scope, _))
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.trace(inits_, deps_, accs.map(name => name: Name), bound.map(name => name: Name)): (accs_, bound_) =>
          val scope_ = scope ++ (accs_ ++ bound_)
          updates.map(update => this.update(scope_, update))

      case Combinator("maps", Nil, deps, bound, List(update)) =>
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.map(deps_, bound.map(name => name: Name)): bound_ =>
          this.update(scope ++ bound_, update)

      case Combinator("invs", Nil, deps, bound, List(List((_, body)))) =>
        val deps_ = deps.map(resolve(scope, _))
        state.exprs.all(deps_, bound.map(name => name: Name)): bound_ =>
          resolve(scope ++ bound_, body)

      // the value at the entry of the method
      case App("old", List(arg)) =>
        state.exprs.old(resolve(scope, arg))

      // the temporal operators, whose arities are checked with the types (see Type.check); a prefix operator without
      // operand comes from an operator of higher precedence before it, e.g. !always p, which needs !(always p)
      case App(op, Nil) if core.Prop.ops.contains(Name(op, None)) =>
        Error.raise("temporal operator without operand, parenthesize it after operators that bind tighter, e.g. !(always p)", op)

      case App(op, args) if core.Prop.ops.contains(Name(op, None)) =>
        core.Prop(Name(op, None), args.map(resolve(scope, _)))

      // placeholders of the verification conditions of temporal properties, e.g. ω₃(x, y), which are not declared
      case App(op, args) if core.Prop.isPlaceholder(op) && !state.funs.contains((op, args.length)) =>
        core.Prop(op, args.map(resolve(scope, _)))

      // unary + is the identity
      case App("+", List(arg)) =>
        resolve(scope, arg)

      case App("!=", args) =>
        val expr_ = App("not", List(App("=", args)))
        resolve(scope, expr_)

      case Diff(xs, arg) =>
        val xs_ = vars(scope, xs, "unknown variables of derivative")
        val arg_ = resolve(scope, arg)
        state.exprs.diff(xs_, arg_)

      case App(name, Nil) if scope.vars.contains(name) =>
        scope.vars(name)

      // variables of function type applied to arguments, which shadow functions of the same name
      case App(name, args) if scope.vars.contains(name) =>
        apply(scope, scope.vars(name), args)

      // functions, then constants of function type applied to arguments, e.g. f(x) for function f(): int -> int,
      // otherwise the members of the enclosing type, with `this` implicit, e.g. its fields
      case App(fun, args) =>
        if state.funs.contains((fun, args.length))
        then state.exprs.app(fun, args.map(resolve(scope, _)))
        else if state.funs.contains((fun, 0))
        then apply(scope, state.exprs.app(fun, Nil), args)
        else if isMember(scope, fun, args.length)
        then resolve(scope, Inner(App("this", Nil), List(Member(fun, args))))
        else
          static(scope, fun, args.length) match
            case Some(qname) => state.exprs.app(qname, args.map(resolve(scope, _)))
            case None        => Error.raise("unresolved identifier", fun)

      // static functions of a type, qualified by its name, T.f(args)
      case Inner(App(name, Nil), Member(fun, args) :: rest) if !scope.vars.contains(name) && state.funs.contains((name + "_" + fun, args.length)) =>
        val base_ = state.exprs.app(name + "_" + fun, args.map(resolve(scope, _)))
        resolve(scope, base_, rest)

      case Inner(base, access) =>
        val base_ = resolve(scope, base)
        resolve(scope, base_, access)

      // patterns are constructors applied to patterns, variables, and wildcards _, which are named apart,
      // and tuples of patterns, those of the constructors of tuples, e.g. of a match on several values
      case Match(arg, cases) =>
        val arg_ = resolve(scope, arg)
        val wildcards = Iterator.from(0)

        def pattern(typ: core.Type, pat: Expr): core.Expr =
          pat match
            case App(name, args) if state.constrs.contains(name) =>
              state.exprs.constr(name)(types => (types zip args).map(pattern))

            case Tuple(List(arg)) =>
              pattern(typ, arg)

            case Tuple(args) =>
              state.exprs.constr(core.Tuples.name(args.length))(types => (types zip args).map(pattern))

            case App("_", Nil) =>
              core.Var(Name("_", Some(wildcards.next())), typ)

            case App(name, Nil) =>
              core.Var(Name(name, None), typ)

            case _ =>
              Error.raise("invalid pattern", pat)

        val cases_ =
          for (pat, body) <- cases
          yield
            val pat_ = pattern(arg_.typ, pat)
            core.Case(pat_, resolve(scope ++ pat_.free.toList, body), core.True)

        state.exprs.match_(arg_, cases_)

      case Ite(test, left, True) =>
        resolve(scope, App("=>", List(test, left)))

      case Ite(test, left, right) =>
        val test_ = resolve(scope, test)
        val left_ = resolve(scope, left)
        val right_ = resolve(scope, right)
        state.exprs.app("ite", List(test_, left_, right_))

      case Choice(cases) =>
        update(scope, cases)

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

      case Lam(bound, body) =>
        val bound_ = bound.map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.lam(bound_, body_)

      case Let(bound, args, body) =>
        Error.report("mismatching let", bound, args):
          require(bound.length == args.length)

        val args_ = args.map(resolve(scope, _))
        val bound_ = bound.map(resolve(scope, _))
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.exprs.let(bound_, args_, body_)

      case Star =>
        Error.raise("* outside of the right-hand side of an assignment")

      case _ =>
        Error.raise("unknown expression", expr)

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

      // the variables assigned * are havocked after the parallel assignment of the others,
      // which are disjoint, such that the other right-hand sides read the values before the assignment
      case Assign(lhs, rhs) if rhs.contains(Star) =>
        Error.report("mismatching assignment", lhs, rhs):
          require(lhs.length == rhs.length)

        val (stars, others) = (lhs zip rhs).partition(_._2 == Star)
        Error.report("arbitrary values of elements are not supported", stars.map(_._1.name)):
          require(stars.forall(_._1.indices.isEmpty))

        val havoc = state.progs.havoc(vars(scope, stars.map(_._1.name), "unknown local variables"))
        if others.isEmpty
        then havoc
        else state.progs.block(Nil, List(resolve(scope, Assign(others.map(_._1), others.map(_._2))), havoc))

      // calls to top-level methods, with or without results
      case Assign(lhs, List(Inner(App(name, args), Nil))) if state.procs.contains(name) =>
        val lhs_ = results(scope, lhs)
        val args_ = args.map(resolve(scope, _))
        state.progs.call(name, args_, lhs_)

      // calls to the methods of the enclosing type, with `this` implicit, and to its static methods
      case Assign(lhs, List(Inner(App(name, args), Nil))) if isMember(scope, name, args.length) =>
        resolve(scope, Assign(lhs, List(Inner(App("this", Nil), List(Member(name, args))))))

      case Assign(lhs, List(Inner(App(name, args), Nil))) if static(scope, name, args.length).exists(state.procs.contains(_)) =>
        val lhs_ = results(scope, lhs)
        val args_ = args.map(resolve(scope, _))
        state.progs.call(static(scope, name, args.length).get, args_, lhs_)

      // static methods of a type, qualified by its name, x := T.m(args)
      case Assign(lhs, List(Inner(App(name, Nil), List(Member(meth, args))))) if !scope.vars.contains(name) && state.procs.contains(name + "_" + meth) =>
        val lhs_ = results(scope, lhs)
        val args_ = args.map(resolve(scope, _))
        state.progs.call(name + "_" + meth, args_, lhs_)

      // all method calls must be top-level on variables, other members are functions (see the access of members)
      case Assign(lhs, List(rhs @ Inner(App(base, Nil), List(Member(fun, args))))) =>
        resolve(scope, App(base, Nil)) match
          case self: core.Var if state.procs.contains(member(self, fun)) =>
            val lhs_ = results(scope, lhs)
            val args_ = args.map(resolve(scope, _))
            state.progs.call(member(self, fun), self :: args_, lhs_)

          case _ =>
            assign(scope, lhs, List(resolve(scope, rhs)))

      case Assign(Nil, rhs) =>
        Error.raise("statement must be a method call", rhs)

      case Assign(lhs, rhs) =>
        assign(scope, lhs, rhs.map(resolve(scope, _)))

      // locals must not shadow variables in scope, therefore their initial values
      // can be resolved together with the block as assignments at its beginning
      case Block(locals, progs) =>
        val locals_ = locals.flatMap(_.vars).map(resolve(scope, _))
        val shadowed = locals_.filter(x => scope.vars.contains(x.name))

        Error.report("local variables shadow variables in scope", shadowed):
          require(shadowed.isEmpty)

        val inits =
          for case Local(vars, Some(rhs)) <- locals
          yield Assign(vars.map((x, _) => Lhs(x, Nil)), rhs)

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

      // verification supports calls only (see VCGen)
      case Par(progs) =>
        val progs_ = progs.map(resolve(scope, _))
        state.progs.par(progs_)

      // the evolution constraint defaults to true
      // the time is bound on real in the right hand sides, the evolution constraint, and the invariants
      case Ode(time, xs, rhs, dom, invs) =>
        val xs_ = vars(scope, xs, "unknown local variables")
        val time_ = core.Var(time, core.Sort.real)
        val scope_ = scope ++ List(time_)
        val rhs_ = rhs.map(resolve(scope_, _))
        val dom_ = dom.map(resolve(scope_, _)).getOrElse(core.True)
        val attrs_ = invariants(scope_, invs, Nil)
        state.progs.ode(time_, xs_, rhs_, dom_, attrs_)
