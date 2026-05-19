package cuvee.boogie

import cuvee.sexpr._

object Syntax:
  import easyparse._

  def kw(text: String) =
    Kw(text)

  def id(name: String) =
    Id(name)

  def pair(arg1: Any, arg2: Any): Any =
    List(arg1, arg2)

  def const(fun: String): Any =
    List(Id(fun))

  def unary(fun: String)(arg1: Any): Any =
    List(Id(fun), arg1)

  def binary(fun: String)(arg1: Any, arg2: Any): Any =
    List(Id(fun), arg1, arg2)

  def ternary(fun: String)(arg1: Any, arg2: Any, arg3: Any): Any =
    List(Id(fun), arg1, arg2, arg3)

  def infix(fun: String, args: List[Any]): Any =
    app(Id(fun), args)

  def app(fun: Id, args: List[Any]): Any =
    fun match
      case Id("!=") =>
        List(Id("not"), Id("=") :: args)

      case Id(name) if translate.contains(name) =>
        Id(translate(name)) :: args

      case _ =>
        fun :: args

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
        List(Id("declare-sort"), sort, args)

      case Some(typ) =>
        List(Id("define-sort"), sort, args, typ)

  def fundef(fun: Id, params: List[Any], args: List[Any], res: Any, rhs: Option[Any]) =
    rhs match
      case None =>
        List(Id("declare-fun"), fun, params, args, res)

      case Some(expr) =>
        List(Id("define-fun"), fun, params, args, res, expr)

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
    "<==>" -> "=",
    "==>" -> "=>",
    "&&" -> "and",
    "||" -> "or",
    "==" -> "=",
    "/" -> "div",
    "%" -> "mod",
    "!" -> "not"
  )
