package cuvee.core

import scala.annotation.targetName

import cuvee.Error

case class Subst[T <: Type, E <: Expr](params: Map[Param, T], vars: Map[Var, E]):
  def inst = params.keySet
  def bound = vars.keySet
  def free = vars.values.free

  def avoid(bound: List[Var]) =
    val captured = bound.filter(free)
    val alpha = Map(captured zip captured.fresh*)

    val rename = Subst(params, alpha)
    val that = Subst(params, vars -- bound ++ alpha)

    (rename, that)

  def apply(p: Param): T | Param =
    params.getOrElse(p, p)

  def apply(x: Var): E | Var =
    vars.getOrElse(x, x)

  def apply(typ: Type): Type =
    typ match
      case p: Param =>
        this(p)

      case Sort(con, args) =>
        Sort(con, this(args))

  def apply(expr: Expr): Expr =
    expr match
      case x: Var =>
        this(x)

      case Lit(value, typ) =>
        Lit(value, this(typ))

      case App(fun, inst, args) =>
        App(fun, this(inst), this(args))

      case Bind(quant, bound, body) =>
        val (rename, that) = avoid(bound)
        Bind(quant, rename(bound), that(body))

      case Let(bound, args, body) =>
        val (rename, that) = avoid(bound)
        Let(rename(bound), this(args), that(body))

  @targetName("Subst.applyParams")
  def apply(params: List[Param]): List[Param | T] =
    for p <- params
    yield this(p)

  @targetName("Subst.applyTypes")
  def apply(types: List[Type]): List[Type] =
    for typ <- types
    yield this(typ)

  @targetName("Subst.applyVars")
  def apply(vars: List[Var]): List[Var | E] =
    for x <- vars
    yield this(x)

  @targetName("Subst.applyExprs")
  def apply(exprs: List[Expr]): List[Expr] =
    for expr <- exprs
    yield this(expr)
