package cuvee.core

import util.Counter
import util.backtrack

import cuvee.Name
import cuvee.Error

case class Con(name: Name, arity: Int)

sealed trait Type:
  def name: Name
  def params: Set[Param]
  def sig: Option[Sig]

case class Param(name: Name) extends Type:
  def params = Set(this)
  def sig = None

  def asIndex = (name, this)

  def fresh =
    Param(name.withIndex(Param.next()))

case class Sort(con: Con, args: List[Type]) extends Type:
  def name = con.name
  def params = args.params
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

object Sort:
  val bool = Sort(Con.bool, Nil)
  val int = Sort(Con.int, Nil)
  val real = Sort(Con.real, Nil)
  val string = Sort(Con.string, Nil)

  def array(dom: Type, ran: Type) =
    Sort(Con.array, List(dom, ran))

object Type:
  import util.Ref

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

  def unify(scope: Scope, typ1: Type, typ2: Type, subst: Ref[Subst[Type, Expr]]): Unit =
    (typ1, typ2) match
      case _ if typ1 == typ2 =>

      case (a1: Param, _) if subst.inst.contains(a1) =>
        unify(scope, subst(a1), typ2, subst)

      case (_, a2: Param) if subst.inst.contains(a2) =>
        unify(scope, typ1, subst(a2), subst)

      case (a1: Param, _) if !rigid(scope, a1) =>
        // occurs check
        if resolve(subst, typ2).params.contains(a1)
        then backtrack

        subst := { subst + (a1 -> typ2) }

      case (_, a2: Param) if !rigid(scope, a2) =>
        unify(scope, a2, typ1, subst)

      case (Sort(con1, args1), Sort(con2, args2)) if con1 == con2 =>
        unify(scope, args1, args2, subst)

      case _ =>
        backtrack

  def unify(scope: Scope, types1: List[Type], types2: List[Type], subst: Ref[Subst[Type, Expr]]): Unit =
    (types1, types2) match
      case (Nil, Nil) =>

      case (typ1 :: types1, typ2 :: types2) =>
        unify(scope, typ1, typ2, subst)
        unify(scope, types1, types2, subst)

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
  def check(scope: Scope, expr: Expr, res: Type, subst: Ref[Subst[Type, Expr]]): Unit =
    expr match
      case Var(name, typ) =>
        Error.report("type mismatch", expr, typ, res):
          unify(scope, typ, res, subst)

      case Lit(value, typ) =>
        Error.report("type mismatch", expr, typ, res):
          unify(scope, typ, res, subst)

      case App(fun, inst, typ, args) =>
        Error.report("wrong number of arguments", fun, args):
          require(inst.length == args.length)

        check(scope, args, inst, subst)

        Error.report("type mismatch", expr, typ, res):
          unify(scope, typ, res, subst)

      case Bind(quant, bound, body) =>
        check(scope, body, Sort.bool, subst)

        Error.report("type mismatch", expr, Sort.bool, res):
          unify(scope, Sort.bool, res, subst)

      case Let(bound, args, body) =>
        check(scope, args, bound.types, subst)
        check(scope, body, res, subst)

  def check(scope: Scope, exprs: List[Expr], types: List[Type], subst: Ref[Subst[Type, Expr]]): Unit =
    for (expr, typ) <- exprs zip types
    do check(scope, expr, typ, subst)

  def check(scope: Scope, expr: Expr, res: Type): Expr =
    val subst = Ref[Subst[Type, Expr]](Subst(Map(), Map()))
    check(scope, expr, res, subst)

    val expr_ = close(subst)(expr)
    val missed = expr_.params -- scope.params.values.toSet

    Error.report("type error: uninstantiated type variables", expr, res, subst.value, missed):
      require(missed.isEmpty)

    expr_

  // well-formedness of programs: assignments match up, break and continue occur inside loops only,
  // and all expressions are well-typed, variables in `fixed`, e.g. the inputs of a procedure, must not be assigned;
  // variables are not checked for being declared, since unknown names are rejected already when resolving them
  def check(scope: Scope, fixed: Set[Var], prog: Prog): Prog =
    check(scope, fixed, prog, false)

  def check(scope: Scope, fixed: Set[Var], prog: Prog, loop: Boolean): Prog =
    prog match
      case Break | Continue =>
        Error.report("break or continue outside of loop", prog):
          require(loop)
        prog

      case Return =>
        prog

      case Spec(xs, pre, post) =>
        assignable(fixed, xs)
        val pre_ = formula(scope, pre)
        val post_ = formula(scope, post)
        Spec(xs, pre_, post_)

      case Assign(lhs, rhs) =>
        assignable(fixed, lhs)

        Error.report("mismatching assignment", lhs, rhs):
          require(lhs.length == rhs.length)

        val rhs_ =
          for (x, e) <- lhs zip rhs
          yield check(scope, e, x.typ)

        Assign(lhs, rhs_)

      // the signature of the procedure is not known here, only the arguments are checked individually
      case Call(proc, args, res) =>
        assignable(fixed, res)

        val args_ =
          for e <- args
          yield check(scope, e, e.typ)

        Call(proc, args_, res)

      case Block(locals, progs) =>
        Error.report("duplicate local variables", locals):
          require(locals.distinctBy(_.name) == locals)

        // locals shadow fixed variables of the same name
        val scope_ = scope ++ locals
        val fixed_ = fixed.filterNot(x => locals.exists(_.name == x.name))
        val progs_ = progs.map(check(scope_, fixed_, _, loop))
        Block(locals, progs_)

      case Choice(progs) =>
        val progs_ = progs.map(check(scope, fixed, _, loop))
        Choice(progs_)

      case If(test, left, right) =>
        val test_ = formula(scope, test)
        val left_ = check(scope, fixed, left, loop)
        val right_ = check(scope, fixed, right, loop)
        If(test_, left_, right_)

      case While(test, body, attrs) =>
        val test_ = formula(scope, test)
        val body_ = check(scope, fixed, body, true)
        While(test_, body_, attrs)

  def formula(scope: Scope, phi: Expr) =
    check(scope, phi, Sort.bool)

  // assigned variables must be distinct and must not be in `fixed`
  def assignable(fixed: Set[Var], xs: List[Var]) =
    Error.report("duplicate variables", xs):
      require(xs.distinct == xs)

    val wrong = xs.filter(fixed)

    Error.report("assignment to variables that must not be modified", wrong):
      require(wrong.isEmpty)
