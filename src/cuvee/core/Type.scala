package cuvee.core

import util.Counter
import util.backtrack

import util.Name
import cuvee.Error

case class Con(name: Name, arity: Int)

sealed trait Type:
  def name: Name
  def params: Set[Param]
  // the sort constructors that occur in the type
  def cons: Set[Con]
  def sig: Option[Sig]

case class Param(name: Name) extends Type:
  def params = Set(this)
  def cons = Set()
  def sig = None

  def asIndex = (name, this)

  def fresh =
    Param(name.withIndex(Param.next()))

case class Sort(con: Con, args: List[Type]) extends Type:
  def name = con.name
  def params = args.params
  def cons = args.cons + con
  def sig = Some(Sig(con.name, args.sig))

object Param extends Counter:
  val a = Param("a")
  val b = Param("b")

object Con:
  val bool = Con("Bool", 0)
  val int = Con("Int", 0)
  val real = Con("Real", 0)
  val string = Con("String", 0)
  val array = Con("Array", 2)
  val seq = Con("Seq", 1)

object Sort:
  val bool = Sort(Con.bool, Nil)
  val int = Sort(Con.int, Nil)
  val real = Sort(Con.real, Nil)
  val string = Sort(Con.string, Nil)

  def array(dom: Type, ran: Type) =
    Sort(Con.array, List(dom, ran))

  def seq(elem: Type) =
    Sort(Con.seq, List(elem))

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

  def close(subst: Subst[Type, Expr]): Subst[Type, Expr] =
    val params_ =
      for (p, typ) <- subst.params
      yield p -> resolve(subst, typ)

    Subst(params_, subst.vars)

  // replace a defined sort by its definition, at the top only
  def unfold(state: State, typ: Type): Type =
    typ match
      case Sort(con, args) if state.sortdefs.contains(con.name) =>
        val (params, body) = state.sortdefs(con.name)
        unfold(state, Subst.from(params, args)(body))

      case _ =>
        typ

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
  // parameters occurring in `types` are treated as rigid
  def bind(pats: List[Type], types: List[Type]): Subst[Type, Nothing] =
    val subst = Ref[Subst[Type, Nothing]](Subst(Map(), Map()))
    bind(pats, types, subst)
    subst.value

  def bind(pat: Type, typ: Type, subst: Ref[Subst[Type, Nothing]]): Unit =
    (pat, typ) match
      case (p: Param, _) if subst.inst.contains(p) =>
        Error.report("type mismatch", p, subst(p), typ):
          require(subst(p) == typ)

      case (p: Param, _) =>
        subst := { subst + (p -> typ) }

      case (Sort(con1, args1), Sort(con2, args2)) if con1 == con2 =>
        bind(args1, args2, subst)

      case _ =>
        Error.raise("type mismatch", pat, typ)

  def bind(pats: List[Type], types: List[Type], subst: Ref[Subst[Type, Nothing]]): Unit =
    Error.report("mismatching length", pats, types):
      require(pats.length == types.length)

    for (pat, typ) <- pats zip types
    do bind(pat, typ, subst)

  // the types of expressions are already instantiated with fresh parameters by the parsers,
  // in particular `inst` of an application holds the expected types of the arguments
  def check(state: State, scope: Scope, expr: Expr, res: Type, subst: Ref[Subst[Type, Expr]]): Unit =
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

        check(state, scope, args, inst, subst)

        Error.report("type mismatch", expr, typ, res):
          unify(state, scope, typ, res, subst)

      // all expressions have the type of the first one
      case Distinct(exprs) =>
        check(state, scope, exprs, exprs.map(_ => exprs.head.typ), subst)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(state, scope, Sort.bool, res, subst)

      // the type parameters of the constructor are instantiated freshly
      case Is(arg, fun) =>
        val su = Subst.fresh(fun.params)
        check(state, scope, arg, su(fun.res), subst)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(state, scope, Sort.bool, res, subst)

      // derivatives are with respect to variables on Real only
      case Diff(xs, arg) =>
        val wrong = xs.filterNot(x => unfold(state, x.typ) == Sort.real)
        Error.report("derivative with respect to variables that are not real", expr, wrong):
          require(wrong.isEmpty)

        check(state, scope, arg, res, subst)

      case Old(arg) =>
        check(state, scope, arg, res, subst)

      case As(arg, typ) =>
        check(state, scope, arg, typ, subst)

        Error.report("type mismatch", expr, typ, res):
          unify(state, scope, typ, res, subst)

      case Bind(quant, bound, body) =>
        check(state, scope, body, Sort.bool, subst)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(state, scope, Sort.bool, res, subst)

      case Let(bound, args, body) =>
        check(state, scope, args, bound.types, subst)
        check(state, scope, body, res, subst)

  def check(state: State, scope: Scope, exprs: List[Expr], types: List[Type], subst: Ref[Subst[Type, Expr]]): Unit =
    for (expr, typ) <- exprs zip types
    do check(state, scope, expr, typ, subst)

  def check(state: State, scope: Scope, expr: Expr, res: Type): Expr =
    val subst = Ref[Subst[Type, Expr]](Subst(Map(), Map()))
    check(state, scope, expr, res, subst)
    instantiate(scope, subst, List(expr)).head

  // apply the solution of the type constraints, all type parameters must be determined
  def instantiate(scope: Scope, subst: Ref[Subst[Type, Expr]], exprs: List[Expr]): List[Expr] =
    val exprs_ = close(subst)(exprs)
    val missed = exprs_.params -- scope.params.values.toSet

    Error.report("type error: uninstantiated type variables", exprs, subst.value, missed):
      require(missed.isEmpty)

    exprs_

  // well-formedness of programs: assignments match up, break and continue occur inside loops only,
  // and all expressions are well-typed, variables in `fixed`, e.g. the inputs of a procedure, must not be assigned;
  // variables are not checked for being declared, since unknown names are rejected already when resolving them
  def check(state: State, scope: Scope, fixed: Set[Var], prog: Prog): Prog =
    check(state, scope, fixed, prog, false)

  def check(state: State, scope: Scope, fixed: Set[Var], prog: Prog, loop: Boolean): Prog =
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

        val Proc(_, params, in, out) = state.procs(name)

        Error.report("wrong number of arguments or results in call", name, args, res):
          require(in.length == args.length && out.length == res.length)

        val su = Subst.fresh(params)
        val subst = Ref[Subst[Type, Expr]](Subst(Map(), Map()))
        check(state, scope, args, su(in.types), subst)

        Error.report("type mismatch in results of call", name, res, out):
          unify(state, scope, res.types, su(out.types), subst)

        val args_ = instantiate(scope, subst, args)
        Call(name, args_, res)

      case Block(locals, progs) =>
        Error.report("duplicate local variables", locals):
          require(locals.distinctBy(_.name) == locals)

        // locals shadow fixed variables of the same name
        val scope_ = scope ++ locals
        val fixed_ = fixed.filterNot(x => locals.exists(_.name == x.name))
        val progs_ = progs.map(check(state, scope_, fixed_, _, loop))
        Block(locals, progs_)

      case Choice(progs) =>
        val progs_ = progs.map(check(state, scope, fixed, _, loop))
        Choice(progs_)

      case If(test, left, right) =>
        val test_ = formula(state, scope, test)
        val left_ = check(state, scope, fixed, left, loop)
        val right_ = check(state, scope, fixed, right, loop)
        If(test_, left_, right_)

      case While(test, body, attrs) =>
        val test_ = formula(state, scope, test)
        val body_ = check(state, scope, fixed, body, true)
        While(test_, body_, attrs)

      case Iter(body, attrs) =>
        val body_ = check(state, scope, fixed, body, true)
        Iter(body_, attrs)

      // differential equations are on Real only, like derivatives
      case Ode(xs, rhs, dom, attrs) =>
        assignable(fixed, xs)

        val wrong = xs.filterNot(x => unfold(state, x.typ) == Sort.real)
        Error.report("differential equations for variables that are not real", wrong):
          require(wrong.isEmpty)

        Error.report("mismatching differential equations", xs, rhs):
          require(xs.length == rhs.length)

        val rhs_ =
          for (x, e) <- xs zip rhs
          yield check(state, scope, e, x.typ)

        val dom_ = formula(state, scope, dom)
        Ode(xs, rhs_, dom_, attrs)

  def formula(state: State, scope: Scope, phi: Expr) =
    check(state, scope, phi, Sort.bool)

  // assigned variables must be distinct and must not be in `fixed`
  def assignable(fixed: Set[Var], xs: List[Var]) =
    Error.report("duplicate variables", xs):
      require(xs.distinct == xs)

    val wrong = xs.filter(fixed)

    Error.report("assignment to variables that must not be modified", wrong):
      require(wrong.isEmpty)
