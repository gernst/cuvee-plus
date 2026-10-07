package cuvee.core

import util.Counter
import util.backtrack

import scala.annotation.targetName

import util.Name
import cuvee.Error

// a sort constructor with its number of arguments
case class Con(name: Name, arity: Int)

// types are type parameters or applications of sort constructors
sealed trait Type:
  def name: Name
  def params: Set[Param]
  // the sort constructors that occur in the type
  def cons: Set[Con]
  def sig: Option[Sig]

// a type parameter, which is rigid inside the declaration that introduces it (see rigid),
// and is instantiated freshly at each use otherwise
case class Param(name: Name) extends Type:
  def params = Set(this)
  def cons = Set()
  def sig = None

  def asIndex = (name, this)

  def fresh =
    Param(name.withIndex(Param.next()))

case class Sort(con: Con, args: List[Type]) extends Type:
  // apply `f` to the arguments
  def map(f: Type => Type) =
    Sort(con, args.map(f))

  def name = con.name
  def params = args.params
  def cons = args.cons + con
  def sig = Some(Sig(con.name, args.sig))

// the counter for fresh type parameters
// bitvectors of width n, (_ BitVec n) in SMT-LIB, whose functions are instantiated per width (see BitVecs)
case class BitVec(n: Int) extends Type:
  def name = Name("BitVec", None)
  def params = Set()
  def cons = Set()
  def sig = Some(Sig(Name("BitVec", Some(n)), Nil))

// the counter for fresh type parameters
object Param extends Counter:
  // the type parameters of the built-in functions and the preludes, a$0 and a$1, written a₀ and a₁ in Dafny and Boogie
  val a = Param(Name("a", Some(0)))
  val b = Param(Name("a", Some(1)))

object Con:
  val bool = Con("Bool", 0)
  val int = Con("Int", 0)
  val real = Con("Real", 0)
  val string = Con("String", 0)
  val array = Con("Array", 2)
  val seq = Con("Seq", 1)
  // finite sets and multisets as in cvc5
  val set = Con("Set", 1)
  val bag = Con("Bag", 1)
  // finite maps, which no solver supports (see Fun.map)
  val map = Con("Map", 2)
  val trace = Con("Trace", 1)

object Sort:
  val bool = Sort(Con.bool, Nil)
  val int = Sort(Con.int, Nil)
  val real = Sort(Con.real, Nil)
  val string = Sort(Con.string, Nil)

  def array(dom: Type, ran: Type) =
    Sort(Con.array, List(dom, ran))

  def seq(elem: Type) =
    Sort(Con.seq, List(elem))

  def set(elem: Type) =
    Sort(Con.set, List(elem))

  def bag(elem: Type) =
    Sort(Con.bag, List(elem))

  def map(key: Type, value: Type) =
    Sort(Con.map, List(key, value))

  // the non-empty sequences of values of a variable at the loop head, see Trace
  def trace(elem: Type) =
    Sort(Con.trace, List(elem))

object Type:
  import util.Ref

  // TODO: structural ordering, for now by the printed representation
  given Ordering[Type] = Ordering.by(_.toString)

  def params(name: String, count: Int) =
    for index <- List.range(0, count)
    yield Param(Name(name, Some(index)))

  // type parameters of the enclosing declaration cannot be instantiated
  def rigid(scope: Scope, p: Param) =
    scope.params.get(p.name) == Some(p)

  // apply `subst` until no bound parameters remain
  def resolve(subst: Subst[Type, Expr], typ: Type): Type =
    val typ_ = subst(typ)
    if typ_ == typ
    then typ
    else resolve(subst, typ_)

  // the substitution with each type resolved, i.e., idempotent
  def close(subst: Subst[Type, Expr]): Subst[Type, Expr] =
    val params_ =
      for (p, typ) <- subst.params
      yield p -> resolve(subst, typ)

    Subst(params_, subst.vars)

  // the type of the elements of a sequence, which is a fresh parameter if it is not known yet,
  // e.g. for the bound variables of the combinators, which is then determined by type checking
  def elem(typ: Type): Type =
    typ match
      case Sort(Con.seq, List(elem)) => elem
      case _                         => Param("a").fresh

  // replace a defined sort by its definition, at the top only
  def unfold(state: State, typ: Type): Type =
    typ match
      case Sort(con, args) if state.sortdefs.contains(con.name) =>
        val (params, body) = state.sortdefs(con.name)
        unfold(state, Subst.from(params, args)(body))

      case _ =>
        typ

  // replace defined sorts by their definitions, also in the arguments
  def expand(state: State, typ: Type): Type =
    unfold(state, typ) match
      case Sort(con, args) => Sort(con, args.map(expand(state, _)))
      case typ_            => typ_

  // the defined sorts are expanded in all types of expressions and programs once they are type checked (see State.exprs),
  // including the variables, also those bound by quantifiers, but not in declarations, e.g. not in formal parameters,
  // which are expanded instead where they meet expressions, e.g. when a procedure is verified
  def expand(state: State, x: Var): Var =
    Var(x.name, expand(state, x.typ))

  @targetName("expandVars")
  def expand(state: State, xs: List[Var]): List[Var] =
    xs.map(expand(state, _))

  def expand(state: State, expr: Expr): Expr =
    def e(expr: Expr) = expand(state, expr)
    def xs(xs: List[Var]) = expand(state, xs)
    def t(typ: Type) = expand(state, typ)

    expr match
      case x: Var                              => expand(state, x)
      case Lit(value, typ)                     => Lit(value, t(typ))
      case App(fun, inst, typ, args)           => App(fun, inst.map(t), t(typ), args.map(e))
      case As(arg, typ)                        => As(e(arg), t(typ))
      case Diff(ys, arg)                       => Diff(xs(ys), e(arg))
      case Trace(init, deps, acc, bound, upds) => Trace(e(init), deps.map(e), expand(state, acc), xs(bound), upds.map(e))
      case Maps(deps, bound, upds)             => Maps(deps.map(e), xs(bound), upds.map(e))
      case Invs(deps, bound, body)             => Invs(deps.map(e), xs(bound), e(body))
      case Bind(quant, bound, body)            => Bind(quant, xs(bound), e(body))
      case Let(bound, args, body)              => Let(xs(bound), args.map(e), e(body))
      case Match(arg, cases)                   => Match(e(arg), cases.map(c => Case(e(c.pat), e(c.body), e(c.cond))))
      case _                                   => expr.map(e)

  // the attributes, whose values are expressions and lists of variables (modifies)
  def expand(state: State, attrs: Attrs): Attrs =
    val attrs_ =
      for (kw, arg) <- attrs.attrs
      yield arg match
        case Some(expr: Expr)  => (kw, Some(expand(state, expr)))
        case Some(ys: List[?]) => (kw, Some(ys.map { case x: Var => expand(state, x); case y => y }))
        case _                 => (kw, arg)

    Attrs(attrs_)

  def expand(state: State, prog: Prog): Prog =
    def e(expr: Expr) = expand(state, expr)
    def p(prog: Prog) = expand(state, prog)
    def xs(xs: List[Var]) = expand(state, xs)
    def a(attrs: Attrs) = expand(state, attrs)
    def call(c: Call) = Call(c.proc, c.args.map(e), xs(c.res))

    prog match
      case Spec(ys, pre, post)         => Spec(xs(ys), e(pre), e(post))
      case Assign(lhs, rhs)            => Assign(xs(lhs), rhs.map(e))
      case c: Call                     => call(c)
      case Block(locals, progs)        => Block(xs(locals), progs.map(p))
      case While(test, body, attrs)    => While(e(test), p(body), a(attrs))
      case Iter(body, attrs)           => Iter(p(body), a(attrs))
      case Ode(t, ys, rhs, dom, attrs) => Ode(expand(state, t), xs(ys), rhs.map(e), e(dom), a(attrs))
      case Par(calls)                  => Par(calls.map(call))
      case _                           => prog.map(e, p)

  // extend `subst` such that the types become equal, backtracks if they cannot be unified;
  // the parameters of the scope are rigid, defined sorts are unfolded as needed
  def unify(state: State, scope: Scope, typ1: Type, typ2: Type, subst: Ref[Subst[Type, Expr]]): Unit =
    (typ1, typ2) match
      case _ if typ1 == typ2 =>

      case (a1: Param, _) if subst.inst.contains(a1) =>
        unify(state, scope, subst(a1), typ2, subst)

      case (_, a2: Param) if subst.inst.contains(a2) =>
        unify(state, scope, typ1, subst(a2), subst)

      case (a1: Param, _) if !rigid(scope, a1) =>
        // occurs check
        if resolve(subst, typ2).params.contains(a1)
        then backtrack

        subst := { subst + (a1 -> typ2) }

      case (_, a2: Param) if !rigid(scope, a2) =>
        unify(state, scope, a2, typ1, subst)

      // defined sorts are unfolded before comparing constructors, since their parameters need not occur in the definition
      case (Sort(con1, _), _) if state.sortdefs.contains(con1.name) =>
        unify(state, scope, unfold(state, typ1), typ2, subst)

      case (_, Sort(con2, _)) if state.sortdefs.contains(con2.name) =>
        unify(state, scope, typ1, unfold(state, typ2), subst)

      case (Sort(con1, args1), Sort(con2, args2)) if con1 == con2 =>
        unify(state, scope, args1, args2, subst)

      case _ =>
        backtrack

  def unify(state: State, scope: Scope, types1: List[Type], types2: List[Type], subst: Ref[Subst[Type, Expr]]): Unit =
    (types1, types2) match
      case (Nil, Nil) =>

      case (typ1 :: types1, typ2 :: types2) =>
        unify(state, scope, typ1, typ2, subst)
        unify(state, scope, types1, types2, subst)

      case _ =>
        backtrack

  // one-sided matching: instantiate the parameters in `pats` such that they become equal to `types`,
  // parameters occurring in `types` are treated as rigid, defined sorts are unfolded as needed
  def bind(state: State, pats: List[Type], types: List[Type]): Subst[Type, Nothing] =
    val subst = Ref[Subst[Type, Nothing]](Subst(Map(), Map()))
    bind(state, pats, types, subst)
    subst.value

  // extend `subst` such that `pat` instantiated becomes `typ`, an error if it cannot
  def bind[E <: Expr](state: State, pat: Type, typ: Type, subst: Ref[Subst[Type, E]]): Unit =
    (pat, typ) match
      case _ if pat == typ =>

      case (p: Param, _) if subst.inst.contains(p) =>
        Error.report("type mismatch", p, subst(p), typ):
          require(expand(state, subst(p)) == expand(state, typ))

      case (p: Param, _) =>
        subst := { subst + (p -> typ) }

      // defined sorts are unfolded before comparing constructors, as in unify
      case (Sort(con1, _), _) if state.sortdefs.contains(con1.name) =>
        bind(state, unfold(state, pat), typ, subst)

      case (_, Sort(con2, _)) if state.sortdefs.contains(con2.name) =>
        bind(state, pat, unfold(state, typ), subst)

      case (Sort(con1, args1), Sort(con2, args2)) if con1 == con2 =>
        bind(state, args1, args2, subst)

      case _ =>
        Error.raise("type mismatch", pat, typ)

  def bind[E <: Expr](state: State, pats: List[Type], types: List[Type], subst: Ref[Subst[Type, E]]): Unit =
    Error.report("mismatching length", pats, types):
      require(pats.length == types.length)

    for (pat, typ) <- pats zip types
    do bind(state, pat, typ, subst)

  // extend `subst` by the formal parameters `xs` replaced by `exprs`,
  // where the type parameters in the types of `xs` are instantiated by the types of `exprs`
  @scala.annotation.targetName("bindVars")
  def bind(state: State, xs: List[Var], exprs: List[Expr], subst: Ref[Subst[Type, Expr]]): Unit =
    Error.report("mismatching length", xs, exprs):
      require(xs.length == exprs.length)

    for (x, expr) <- xs zip exprs
    do
      bind(state, x.typ, expr.typ, subst)
      subst := { subst + (x -> expr) }

  // the types of expressions are already instantiated with fresh parameters by the parsers,
  // in particular `inst` of an application holds the expected types of the arguments;
  // `subst` collects the solution of the type equations, `pending` the applications of overloaded operators,
  // whose implementations are determined afterwards (see overload)
  def check(state: State, scope: Scope, expr: Expr, res: Type, subst: Ref[Subst[Type, Expr]], pending: Ref[List[App]]): Unit =
    expr match
      case Var(name, typ) =>
        Error.report("type mismatch", expr, typ, res):
          unify(state, scope, typ, res, subst)

      case Lit(value, typ) =>
        Error.report("type mismatch", expr, typ, res):
          unify(state, scope, typ, res, subst)

      case App(fun, inst, typ, args) =>
        Error.report("wrong number of arguments", fun, args):
          require(inst.length == args.length)

        check(state, scope, args, inst, subst, pending)

        // the implementation is determined later, once the type that it depends on is known
        expr match
          case app @ App(fun, _, _, _) if Overload.isGeneric(fun) => pending := app :: pending.value
          case _                                                  =>

        Error.report("type mismatch", expr, typ, res):
          unify(state, scope, typ, res, subst)

      // all expressions have the type of the first one
      case Distinct(exprs) =>
        check(state, scope, exprs, exprs.map(_ => exprs.head.typ), subst, pending)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(state, scope, Sort.bool, res, subst)

      // the type parameters of the constructor are instantiated freshly
      case Is(arg, fun) =>
        val su = Subst.fresh(fun.params)
        check(state, scope, arg, su(fun.res), subst, pending)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(state, scope, Sort.bool, res, subst)

      // derivatives are with respect to variables on Real only
      case Diff(xs, arg) =>
        val wrong = xs.filterNot(x => unfold(state, x.typ) == Sort.real)
        Error.report("derivative with respect to variables that are not real", expr, wrong):
          require(wrong.isEmpty)

        check(state, scope, arg, res, subst, pending)

      case Old(arg) =>
        check(state, scope, arg, res, subst, pending)

      // the accumulator starts with the initial value and is updated by the results
      case Trace(init, deps, acc, bound, updates) =>
        check(state, scope, init, acc.typ, subst, pending)
        dependencies(state, scope, expr, deps, bound, subst, pending)
        this.updates(state, scope, updates, acc.typ, subst, pending)

        Error.report("type mismatch", expr, Sort.trace(acc.typ), res):
          unify(state, scope, Sort.trace(acc.typ), res, subst)

      // the results have the same type as the first one
      case Maps(deps, bound, updates) =>
        Error.report("map without update", expr):
          require(updates.nonEmpty)

        val typ = updates.head.rhs.typ
        dependencies(state, scope, expr, deps, bound, subst, pending)
        this.updates(state, scope, updates, typ, subst, pending)

        Error.report("type mismatch", expr, Sort.seq(typ), res):
          unify(state, scope, Sort.seq(typ), res, subst)

      case Invs(deps, bound, body) =>
        dependencies(state, scope, expr, deps, bound, subst, pending)
        check(state, scope, body, Sort.bool, subst, pending)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(state, scope, Sort.bool, res, subst)

      case As(arg, typ) =>
        check(state, scope, arg, typ, subst, pending)

        Error.report("type mismatch", expr, typ, res):
          unify(state, scope, typ, res, subst)

      case Bind(quant, bound, body) =>
        check(state, scope, body, Sort.bool, subst, pending)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(state, scope, Sort.bool, res, subst)

      case Let(bound, args, body) =>
        check(state, scope, args, bound.types, subst, pending)
        check(state, scope, body, res, subst, pending)

      // the patterns have the type of the argument, the bodies that of the match
      case Match(arg, cases) =>
        Error.report("match without cases", expr):
          require(cases.nonEmpty)

        val pats = cases.map(_.pat)
        for pat <- pats
        do
          Error.report("invalid pattern", pat):
            require(pattern(state, pat))

        check(state, scope, arg :: pats, (arg :: pats).map(_ => arg.typ), subst, pending)

        for Case(_, body, cond) <- cases
        do
          check(state, scope, cond, Sort.bool, subst, pending)
          check(state, scope, body, res, subst, pending)

  // patterns consist of variables and constructors applied to patterns, where each variable occurs at most once
  def pattern(state: State, pat: Expr): Boolean =
    def vars(pat: Expr): Option[List[Var]] =
      pat match
        case x: Var =>
          Some(List(x))

        case App(fun, _, _, args) if state.constrs.get(fun.name) == Some(fun) =>
          val xs = args.map(vars)
          if xs.forall(_.isDefined) then Some(xs.flatten.flatten) else None

        case _ =>
          None

    vars(pat).exists(xs => xs.distinct.length == xs.length)

  // the dependencies of the combinators are sequences over the types of the bound variables, of which there is at least one
  def dependencies(state: State, scope: Scope, expr: Expr, deps: List[Expr], bound: List[Var], subst: Ref[Subst[Type, Expr]], pending: Ref[List[App]]): Unit =
    Error.report("combinator without dependencies", expr):
      require(deps.nonEmpty)

    Error.report("mismatching dependencies and bound variables", expr, deps, bound):
      require(deps.length == bound.length)

    check(state, scope, deps, bound.map(x => Sort.seq(x.typ)), subst, pending)

  // the guards of updates are formulas, and the results have type `typ`
  def updates(state: State, scope: Scope, updates: List[Upd], typ: Type, subst: Ref[Subst[Type, Expr]], pending: Ref[List[App]]): Unit =
    for Upd(cond, rhs) <- updates
    do
      check(state, scope, cond, Sort.bool, subst, pending)
      check(state, scope, rhs, typ, subst, pending)

  def check(state: State, scope: Scope, exprs: List[Expr], types: List[Type], subst: Ref[Subst[Type, Expr]], pending: Ref[List[App]]): Unit =
    for (expr, typ) <- exprs zip types
    do check(state, scope, expr, typ, subst, pending)

  // `expr` checked against `res`, with the solution of the type constraints applied
  def check(state: State, scope: Scope, expr: Expr, res: Type): Expr =
    val subst = Ref[Subst[Type, Expr]](Subst.empty)
    val pending = Ref[List[App]](Nil)
    check(state, scope, expr, res, subst, pending)
    instantiate(state, scope, subst, pending, List(expr)).head

  // the applications of overloaded operators collected by type checking are deferred constraints:
  // each is checked against the signature of its implementation, once the type of its first argument
  // (see Overload.dispatch) is known, which may determine further types, e.g. of s[0] in s[0] + 1,
  // or of a polymorphic constant c in (c + d) == s[0]; this is repeated as long as some application is decided
  def overload(state: State, scope: Scope, subst: Ref[Subst[Type, Expr]], pending: Ref[List[App]]): Unit =
    val (blocked, ready) = pending.value.partition(app => dispatch(state, subst, app).isInstanceOf[Param])
    pending := blocked

    for app @ App(op, inst, typ, _) <- ready
    do
      val first = dispatch(state, subst, app)

      Overload.impl(op.name, op.arity, first, unfold(state, resolve(subst.value, typ))) match
        case Some(Impl(sig, _)) =>
          val su = Subst.fresh(sig.params)
          Error.report("type mismatch", app, sig):
            unify(state, scope, su(sig.args), inst, subst)
            unify(state, scope, su(sig.res), typ, subst)

        case None =>
          Error.raise("operator not defined for type", op.name, first)

    if ready.nonEmpty
    then overload(state, scope, subst, pending)

  // the type that determines the implementation of an overloaded operator, as far as it is known
  def dispatch(state: State, subst: Ref[Subst[Type, Expr]], app: App): Type =
    val App(op, inst, _, _) = app
    unfold(state, resolve(subst.value, inst(Overload.dispatch(op.name, op.arity))))

  // apply the solution of the type constraints after resolving overloading,
  // all overloaded operators and type parameters must be determined
  def instantiate(state: State, scope: Scope, subst: Ref[Subst[Type, Expr]], pending: Ref[List[App]], exprs: List[Expr]): List[Expr] =
    overload(state, scope, subst, pending)

    // numeric literals whose type is still open are integers, which may decide further overloaded operators,
    // e.g. in 1 + 2, whereas in x + 1 for a bitvector x, the literal is a bitvector
    val open =
      exprs.flatMap(numerals).map(resolve(subst.value, _)).collect:
        case p: Param if !rigid(scope, p) => p

    if open.nonEmpty
    then
      for p <- open.distinct
      do subst := { subst + (p -> Sort.int) }
      overload(state, scope, subst, pending)

    Error.report("ambiguous overloaded operator", pending.value):
      require(pending.value.isEmpty)

    val exprs_ = close(subst)(exprs).map(numeral(state, _))
    val missed = exprs_.params -- scope.params.values.toSet

    Error.report("type error: uninstantiated type variables", missed):
      require(missed.isEmpty)

    exprs_

  // the types of the numeric literals in `expr`, which the frontends may leave open (see instantiate)
  def numerals(expr: Expr): List[Type] =
    val inner = List.newBuilder[Type]
    expr.map: arg =>
      inner ++= numerals(arg)
      arg
    expr match
      case Lit(_: BigInt, typ) => typ :: inner.result()
      case _                   => inner.result()

  // numeric literals of bitvectors are reduced modulo 2^n, those of reals are rationals
  def numeral(state: State, expr: Expr): Expr =
    expr match
      case Lit(value: BigInt, typ) =>
        unfold(state, typ) match
          case Sort.int  => expr
          case BitVec(n) => Lit(value.mod(BigInt(2).pow(n)), typ)
          case Sort.real => Lit(util.Rational(value), typ)
          case typ_      => Error.raise("type mismatch", value, typ_)

      case _ =>
        expr.map(numeral(state, _))

  // well-formedness of programs: assignments match up, break and continue occur inside loops only,
  // and all expressions are well-typed, variables in `fixed`, e.g. the inputs of a procedure, must not be assigned;
  // `mod` are the global variables that may be modified, those in the modifies clause of the procedure
  // and of the innermost loop, which subsumes the global variables that calls modify;
  // variables are not checked for being declared, since unknown names are rejected already when resolving them
  def check(state: State, scope: Scope, fixed: Set[Var], mod: Set[Var], prog: Prog): Prog =
    check(state, scope, fixed, mod, prog, false)

  // `loop` holds inside of loops, where break and continue are allowed
  def check(state: State, scope: Scope, fixed: Set[Var], mod: Set[Var], prog: Prog, loop: Boolean): Prog =
    prog match
      case Break | Continue =>
        Error.report("break or continue outside of loop", prog):
          require(loop)
        prog

      case Return =>
        prog

      case Spec(xs, pre, post) =>
        assignable(fixed, xs)
        val pre_ = formula(state, scope, pre)
        val post_ = formula(state, scope, post)
        Spec(xs, pre_, post_)

      case Assign(lhs, rhs) =>
        assignable(fixed, lhs)

        Error.report("mismatching assignment", lhs, rhs):
          require(lhs.length == rhs.length)

        val rhs_ =
          for (x, e) <- lhs zip rhs
          yield check(state, scope, e, x.typ)

        Assign(lhs, rhs_)

      // arguments and results are checked together against the signature of the procedure,
      // whose type parameters are instantiated freshly
      case Call(name, args, res) =>
        assignable(fixed, res)

        Error.report("procedure not declared", name):
          require(state.procs.contains(name))

        val unknown = state.procattrs(name).modifies.filterNot(mod)
        Error.report("call modifies variables that are not in the modifies clause", name, unknown):
          require(unknown.isEmpty)

        val Proc(_, params, in, out) = state.procs(name)

        Error.report("wrong number of arguments or results in call", name, args, res):
          require(in.length == args.length && out.length == res.length)

        val su = Subst.fresh(params)
        val subst = Ref[Subst[Type, Expr]](Subst.empty)
        val pending = Ref[List[App]](Nil)
        check(state, scope, args, su(in.types), subst, pending)

        Error.report("type mismatch in results of call", name, res, out):
          unify(state, scope, res.types, su(out.types), subst)

        val args_ = instantiate(state, scope, subst, pending, args)
        Call(name, args_, res)

      case Block(locals, progs) =>
        Error.report("duplicate local variables", locals):
          require(locals.distinctBy(_.name) == locals)

        // locals shadow fixed variables of the same name
        val scope_ = scope ++ locals
        val fixed_ = fixed.filterNot(x => locals.exists(_.name == x.name))
        val progs_ = progs.map(check(state, scope_, fixed_, mod, _, loop))
        Block(locals, progs_)

      case Choice(progs) =>
        val progs_ = progs.map(check(state, scope, fixed, mod, _, loop))
        Choice(progs_)

      case If(test, left, right) =>
        val test_ = formula(state, scope, test)
        val left_ = check(state, scope, fixed, mod, left, loop)
        val right_ = check(state, scope, fixed, mod, right, loop)
        If(test_, left_, right_)

      case While(test, body, attrs) =>
        val test_ = formula(state, scope, test)
        val body_ = loop_(state, scope, fixed, mod, body, attrs)
        While(test_, body_, attrs)

      case Iter(body, attrs) =>
        val body_ = loop_(state, scope, fixed, mod, body, attrs)
        Iter(body_, attrs)

      // differential equations are on Real only, like derivatives, and so is the time
      // the history, if it is declared, ticks after the evolution (see Verify) and must be modifiable
      case Ode(time, xs, rhs, dom, attrs) =>
        assignable(fixed, xs)

        val history = state.vars.get("history").toList.filterNot(mod)
        Error.report("differential equation ticks the history, which is not in the modifies clause", history):
          require(history.isEmpty)

        val wrong = (time :: xs).filterNot(x => unfold(state, x.typ) == Sort.real)
        Error.report("differential equations for variables that are not real", wrong):
          require(wrong.isEmpty)

        Error.report("mismatching differential equations", xs, rhs):
          require(xs.length == rhs.length)

        val rhs_ =
          for (x, e) <- xs zip rhs
          yield check(state, scope, e, x.typ)

        val dom_ = formula(state, scope, dom)
        Ode(time, xs, rhs_, dom_, attrs)

      case Par(calls) =>
        val shared = Par.shared(state, calls)
        Error.report("parallel calls share modified variables", shared):
          require(shared.isEmpty)

        val calls_ =
          for call <- calls
          yield (check(state, scope, fixed, mod, call, loop): @unchecked) match
            case call_ : Call => call_
        Par(calls_)

  // the body of a loop modifies the global variables in the modifies clause of the loop only, directly or by calls,
  // which must be global variables that are modifiable outside of the loop
  def loop_(state: State, scope: Scope, fixed: Set[Var], mod: Set[Var], body: Prog, attrs: Attrs): Prog =
    val mod_ = attrs.modifies.toSet

    val nonglobal = mod_ -- state.globals
    Error.report("modifies clause of loop lists variables that are not global", nonglobal):
      require(nonglobal.isEmpty)

    val unknown = mod_ -- mod
    Error.report("modifies clause of loop lists global variables that are not modifiable", unknown):
      require(unknown.isEmpty)

    check(state, scope, fixed ++ (mod -- mod_), mod_, body, true)

  def formula(state: State, scope: Scope, phi: Expr) =
    check(state, scope, phi, Sort.bool)

  // assigned variables must be distinct and must not be in `fixed`
  def assignable(fixed: Set[Var], xs: List[Var]) =
    Error.report("duplicate variables", xs):
      require(xs.distinct == xs)

    val wrong = xs.filter(fixed)

    Error.report("assignment to variables that must not be modified", wrong):
      require(wrong.isEmpty)
