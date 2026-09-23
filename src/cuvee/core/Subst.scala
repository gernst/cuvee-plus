package cuvee.core

import scala.annotation.targetName

import cuvee.Error

object Subst:
  val empty = Subst(Map(), Map())

  @targetName("Subst.freshParams")
  def fresh(params: List[Param]): Subst[Param, Nothing] =
    from(params, params.fresh)

  @targetName("Subst.fromParams")
  def from[T <: Type](params: List[Param], types: List[T]): Subst[T, Nothing] =
    Error.report("mismatching length", params, types):
      require(params.length == types.length)
    Subst(Map(params zip types*), Map())

  @targetName("Subst.freshVars")
  def fresh(vars: List[Var]): Subst[Nothing, Expr] =
    from(vars, vars.fresh)

  @targetName("Subst.fromVars")
  def from[E <: Expr](vars: List[Var], exprs: List[E]): Subst[Nothing, E] =
    Error.report("mismatching length", vars, exprs):
      require(vars.length == exprs.length)
    Subst(Map(), Map(vars zip exprs*))

case class Subst[T <: Type, E <: Expr](params: Map[Param, T], vars: Map[Var, E]):
  def inst = params.keySet
  def bound = vars.keySet
  def free = vars.values.free

  @targetName("Subst.updateParam")
  def +(pair: (Param, T)) =
    Subst(params + pair, vars)

  @targetName("Subst.updateVar")
  def +(pair: (Var, E)) =
    Subst(params, vars + pair)

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

      case App(fun, inst, typ, args) =>
        App(fun, this(inst), this(typ), this(args))

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
