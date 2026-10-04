package cuvee.core

import scala.annotation.targetName

import cuvee.Error

object Subst:
  def empty[T <: Type, E <: Expr] = Subst[T, E](Map(), Map())

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
    // compare by name since bound variables may change their type
    val names = free.map(_.name)
    val captured = bound.filter(x => names.contains(x.name))
    val alpha = Map(captured zip captured.fresh.map(retype)*)

    val rename = Subst(params, alpha)
    val that = Subst(params, vars -- bound ++ alpha)

    (rename, that)

  def apply(p: Param): T | Param =
    params.getOrElse(p, p)

  // variables not in the domain keep their name but have the type parameters substituted
  def apply(x: Var): E | Var =
    vars.getOrElse(x, retype(x))

  def retype(x: Var): Var =
    if params.isEmpty
    then x
    else Var(x.name, this(x.typ))

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

      case Distinct(exprs) =>
        Distinct(this(exprs))

      case Is(expr, fun) =>
        Is(this(expr), fun)

      case As(expr, typ) =>
        As(this(expr), this(typ))

      // the variables of a derivative can only be renamed, like assigned variables
      case Diff(xs, expr) =>
        Diff(lhs(xs), this(expr))

      case Old(expr) =>
        Old(this(expr))

      case Bind(quant, bound, body) =>
        val (rename, that) = avoid(bound)
        Bind(quant, rename(bound), that(body))

      // the accumulator and the bound variables of the combinators are renamed like those of binders
      case Trace(init, deps, acc, bound, update) =>
        val (rename, that) = avoid(acc :: bound)
        Trace(this(init), this(deps), rename.lhs(acc), rename.lhs(bound), for (g, e) <- update yield (that(g), that(e)))

      case TraceMap(deps, bound, update) =>
        val (rename, that) = avoid(bound)
        TraceMap(this(deps), rename.lhs(bound), for (g, e) <- update yield (that(g), that(e)))

      case TraceAll(deps, bound, body) =>
        val (rename, that) = avoid(bound)
        TraceAll(this(deps), rename.lhs(bound), that(body))

      case Let(bound, args, body) =>
        val (rename, that) = avoid(bound)
        Let(rename(bound), this(args), that(body))

  // assigned variables can only be renamed
  def lhs(x: Var): Var =
    this(x) match
      case x_ : Var =>
        x_

      case e =>
        Error.raise("cannot substitute assigned variable", x, e)

  @targetName("Subst.lhsVars")
  def lhs(xs: List[Var]): List[Var] =
    for x <- xs
    yield lhs(x)

  def apply(attrs: Attrs): Attrs =
    val attrs_ =
      for (kw, arg) <- attrs.attrs
      yield arg match
        case Some(expr: Expr) => (kw, Some(this(expr)))
        case _                => (kw, arg)

    Attrs(attrs_)

  def apply(prog: Prog): Prog =
    prog match
      case Break | Continue | Return =>
        prog

      case Spec(xs, pre, post) =>
        Spec(lhs(xs), this(pre), this(post))

      case Assign(xs, rhs) =>
        Assign(lhs(xs), this(rhs))

      case Call(proc, args, res) =>
        Call(proc, this(args), lhs(res))

      case Block(locals, progs) =>
        val (rename, that) = avoid(locals)
        Block(rename.lhs(locals), that(progs))

      case Choice(progs) =>
        Choice(this(progs))

      case If(test, left, right) =>
        If(this(test), this(left), this(right))

      case While(test, body, attrs) =>
        While(this(test), this(body), this(attrs))

      case Iter(body, attrs) =>
        Iter(this(body), this(attrs))

      case Ode(xs, rhs, dom, attrs) =>
        Ode(lhs(xs), this(rhs), this(dom), this(attrs))

      case Par(calls) =>
        Par(for Call(proc, args, res) <- calls yield Call(proc, this(args), lhs(res)))

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

  @targetName("Subst.applyProgs")
  def apply(progs: List[Prog]): List[Prog] =
    for prog <- progs
    yield this(prog)
