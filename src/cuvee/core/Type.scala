package cuvee.core

import util.Counter
import util.backtrack

import cuvee.Name
import cuvee.Error

case class Con(name: Name, arity: Int)
case class Data(params: List[Param], constrs: List[(Fun, List[Fun])])

sealed trait Type:
  def params: Set[Param]

case class Param(name: Name) extends Type:
  def params = Set(this)

  def asIndex = (name, this)

  def fresh =
    Param(name.withIndex(Param.next()))

case class Sort(con: Con, args: List[Type]) extends Type:
  def params = args.params

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

object Type:
  import util.Ref

  def unify(scope: Scope, typ1: Type, typ2: Type, subst: Ref[Subst[Type, Expr]]): Unit =
    (typ1, typ2) match
      case (Param(name), _) if scope.params.contains(name) =>
        backtrack

      case (a1: Param, _) if subst.params.contains(a1) =>
        unify(scope, subst(a1), typ2, subst)

      case (a1: Param, _) =>
        subst := { subst + (a1 -> typ2) }

      case (_, b2: Param) =>
        unify(scope, b2, typ1, subst)

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

  def check(scope: Scope, expr: Expr, res: Type, subst: Ref[Subst[Type, Expr]]): Unit =
    expr match
      case Var(name, typ) =>
        Error.report("type mismatch", expr, typ):
          unify(scope, typ, res, subst)

      case Lit(value, typ) =>
        Error.report("type mismatch", expr, typ):
          unify(scope, typ, res, subst)

      case App(fun, inst, typ, args) =>
        // we expect `inst` to be a list of fresh params (from Parser.expr)
        // therefore orienting the unification this way prefers to instantiate those in `inst`
        val scope_ = scope ++ fun.params

        Error.report("type mismatch", fun, inst, res):
          unify(scope_, inst, fun.args, subst)
          unify(scope_, res, fun.res, subst)
          unify(scope_, typ, fun.res, subst)

      case Bind(quant, bound, body) =>
        Error.report("type mismatch", body, res, Sort.bool):
          check(scope, body, res, subst)
          unify(scope, res, Sort.bool, subst)

      case Let(bound, args, body) =>
        ???

  def check(scope: Scope, expr: Expr, res: Type): Expr =
    val subst = Ref(Subst.empty)
    check(scope, expr, res, subst)

    val expr_ = subst(expr)
    val missed = expr_.params -- scope.params.values.toSet

    Error.report("type error: uninstantiated type variables", expr, res, subst.value, missed):
      require(missed.isEmpty)

    expr_
