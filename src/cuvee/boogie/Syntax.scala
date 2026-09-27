package cuvee.boogie

import cuvee.Error
import cuvee.sexpr._

object Syntax:
  import easyparse._

  def kw(text: String) =
    Kw(text)

  def str(text: String) =
    Str(text)

  def num(text: String) =
    Num(text)

  def id(name: String) =
    if translate.contains(name)
    then Id(translate(name))
    else Id(name)

  def pair(arg1: Any, arg2: Any): Any =
    List(arg1, arg2)

  def const(fun: String): Any =
    id(fun)

  def unary(fun: String)(arg1: Any): Any =
    List(id(fun), arg1)

  def binary(fun: String)(arg1: Any, arg2: Any): Any =
    List(id(fun), arg1, arg2)

  def ternary(fun: String)(arg1: Any, arg2: Any, arg3: Any): Any =
    List(id(fun), arg1, arg2, arg3)

  def nary(fun: String)(args: List[Any]): Any =
    id(fun) :: args

  def infix(fun: String, args: List[Any]): Any =
    app(id(fun), args)

  def app(fun: Id, args: List[Any]): Any =
    fun match
      case Id("!=") =>
        List(Id("not"), Id("=") :: args)

      case _ =>
        if args.isEmpty
        then fun
        else fun :: args

  def app(fun: Id, args: List[Any], access: List[(Any, Option[Any])]): Any =
    zip(app(fun, args), access)

  def zip(base: Any, access: List[(Any, Option[Any])]): Any =
    access match
      case Nil =>
        base

      case (index, None) :: access_ =>
        val base_ = List(Id("select"), base, index)
        zip(base_, access_)

      case (index, Some(value)) :: access_ =>
        val base_ = List(Id("store"), base, index, value)
        zip(base_, access_)

  def datadef(sort: Id, params: List[Any], constrs: List[(Id, List[Any])]) =
    if params.isEmpty
    then List(Id("declare-datatype"), sort, constrs)
    else List(Id("declare-datatype"), sort, List(Id("par"), params, constrs))

  def sortdef(sort: Id, args: List[Any], rhs: Option[Any]) =
    rhs match
      case None =>
        val arity = args.length
        List(Id("declare-sort"), sort, Num(arity.toString))

      case Some(typ) =>
        List(Id("define-sort"), sort, args, typ)

  def invariants(invs: List[Any]) =
    val invs_ =
      for inv <- invs
      yield List(Kw("invariant"), inv)

    invs_.flatten

  def contract(args: List[Any], pre: List[Any], args_ : List[Any], post: List[Any]) =
    val pre_ =
      for phi <- pre
      yield List(Kw("requires"), List(Id("lambda"), args, phi))

    val post_ =
      for phi <- pre
      yield List(Kw("ensures"), List(Id("lambda"), args_, phi))

    pre_.flatten ++ post_.flatten

  def argnames(args: List[Any], args_ : List[Any]) =
    val formals_ =
      if args.nonEmpty
      then List(kw("formals"), args)
      else Nil

    val returns_ =
      if args_.nonEmpty
      then List(kw("returns"), args_)
      else Nil

    formals_ ++ returns_

  def fundef(fun: Id, params: List[Any], args: List[Any], res: Any, pre: List[Any], post: List[Any], rhs: Option[Any]) =
    val names_ = argnames(args, Nil)
    val contract_ = contract(args, pre, args, post)
    val attrs = names_ ++ contract_

    val types_ = args.map { case List(_, typ) => typ }

    (rhs, params) match
      case (None, Nil) =>
        List(Id("declare-fun"), fun, types_, res) ++ attrs

      case (None, _) =>
        List(Id("declare-fun"), fun, List(Id("par"), params, types_, res) ++ attrs)

      case (Some(expr), Nil) =>
        List(Id("define-fun"), fun, args, res, expr) ++ attrs

      case (Some(expr), _) =>
        List(Id("define-fun"), fun, List(Id("par"), params, args, res, expr) ++ attrs)

  def procdef(
      proc: Id,
      params: List[Any],
      in: List[Any],
      out: Option[List[Any]],
      mod: List[List[Any]],
      pre: List[Any],
      post: List[Any],
      body: Option[Any]
  ) =
    val ret = out.toList.flatten
    val names_ = argnames(in, ret)
    val contract_ = contract(in, pre, in ++ ret, post)
    val attrs = names_ ++ contract_

    val in_ = in.map { case List(_, typ) => typ }
    val ret_ = ret.map { case List(_, typ) => typ }

    (params, body) match {
      case (Nil, None) =>
        List(Id("declare-proc"), proc, in_, ret_) ++ attrs

      case (_, None) =>
        List(Id("declare-proc"), proc, List(Id("par"), in_, ret_) ++ attrs)

      case (Nil, Some(prog)) =>
        List(Id("define-proc"), proc, in, ret, prog) ++ attrs

      case (_, Some(prog)) =>
        List(Id("define-proc"), proc, List(Id("par"), in, out, prog) ++ attrs)
    }

  def assign(vars: List[Id], exprs: List[Any]) =
    Error.report("malformed assignment", vars, exprs):
      require(vars.length == exprs.length)

    val pairs =
      for (x, e) <- (vars zip exprs)
      yield List(x, e)

    List(Id("assign")) ++ pairs

  def while_(test: Any, invs: List[Any], body: Any) =
    val attrs_ = invariants(invs)

    val prog = List(Id("while"), test, body)

    if attrs_.nonEmpty
    then List(Id("!"), prog) ++ attrs_
    else prog

  def lemma(justify: String)(attrs: List[Kw], params: List[Any], expr: Any, proof: Option[Any]) =
    val attrs_ =
      proof match
        case None =>
          attrs
        case Some(tactic) =>
          attrs ++ List(Kw("proof"), tactic)

    val expr_ =
      if attrs_.nonEmpty
      then List(Id("!"), expr) ++ attrs_
      else expr

    if params.isEmpty
    then List(Id(justify), expr_)
    else List(Id(justify), List("par", params, expr_))

  val translate = Map(
    "int" -> "Int",
    "bool" -> "Bool",
    "array" -> "Array",
    "<==>" -> "=",
    "==>" -> "=>",
    "&&" -> "and",
    "||" -> "or",
    "==" -> "=",
    "/" -> "div",
    "%" -> "mod",
    "!" -> "not"
  )
