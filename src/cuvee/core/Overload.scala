package cuvee.core

import util.Name
import cuvee.Error

// the arithmetic operators and comparisons, which are implemented by different functions for Int and Real,
// e.g. + by Fun.int.plus on Int and by Fun.real.plus on Real, and on sequences, + is concatenation and <= is prefix;
// the frontends declare them once polymorphically in their preludes, and after type checking,
// each application is replaced by the implementing function for the type of its arguments (see apply),
// such that the generic operators never leave the frontend
object Overload:
  // the implementing function for each operator (name and arity) and sort constructor of its arguments,
  // named as in SMT-LIB, where div and mod are on Int only and / on Real only,
  // except that div on Real is real division, since Dafny's / translates to div on both types
  val table: Map[(Name, Int, Con), Fun] =
    val funs =
      for fun <- Fun.int.all ++ Fun.real.all
      yield
        val Sort(con, _) = fun.args.head: @unchecked
        (fun.name, fun.arity, con) -> fun

    val alias = (Name("div", None), 2, Con.real) -> Fun.real.div
    val seq = List(
      (Name("+", None), 2, Con.seq) -> Fun.seq.concat,
      (Name("<=", None), 2, Con.seq) -> Fun.seq.prefixof
    )
    Map(funs ++ (alias :: seq)*)

  // the overloaded operators (name and arity)
  val generic: Set[(Name, Int)] =
    for (name, arity, _) <- table.keySet
    yield (name, arity)

  // the functions that implement operator `name` with `arity` for some type
  def funs(name: Name, arity: Int): Set[Fun] =
    for
      ((name_, arity_, _), fun) <- table.toSet
      if name_ == name && arity_ == arity
    yield fun

  // the function that implements operator `name` with `arity` for arguments of type `typ`,
  // raises an error if the operator is not defined for that type, e.g. for a type parameter
  def fun(name: Name, arity: Int, typ: Type): Fun =
    val key = typ match
      case Sort(con, _) => Some((name, arity, con))
      case _: Param     => None

    key.flatMap(table.get) match
      case Some(fun) => fun
      case None      => Error.raise("operator not defined for type", name, typ)

  // whether `fun` is the generic declaration of an overloaded operator in the prelude,
  // the resolved functions have no type parameters
  def isGeneric(fun: Fun): Boolean =
    fun.params.nonEmpty && generic.contains((fun.name, fun.arity))

  // replace all overloaded operators in a type checked expression, bottom-up
  def apply(state: State, expr: Expr): Expr =
    expr match
      case _: Var | _: Lit =>
        expr

      case App(fun, inst, typ, args) =>
        val app_ = App(fun, inst, typ, args.map(apply(state, _)))
        if isGeneric(fun)
        then resolve(state, app_)
        else app_

      case Distinct(exprs) =>
        Distinct(exprs.map(apply(state, _)))

      case Is(expr, fun) =>
        Is(apply(state, expr), fun)

      case As(expr, typ) =>
        As(apply(state, expr), typ)

      case Diff(xs, expr) =>
        Diff(xs, apply(state, expr))

      case Bind(quant, bound, body) =>
        Bind(quant, bound, apply(state, body))

      case Let(bound, args, body) =>
        Let(bound, args.map(apply(state, _)), apply(state, body))

  // replace all overloaded operators in the expressions of a type checked program,
  // the attributes of loops are type checked separately by the parsers, which resolves them as well
  def apply(state: State, prog: Prog): Prog =
    prog match
      case Break | Continue | Return =>
        prog

      case Spec(xs, pre, post) =>
        Spec(xs, apply(state, pre), apply(state, post))

      case Assign(lhs, rhs) =>
        Assign(lhs, rhs.map(apply(state, _)))

      case Call(name, args, res) =>
        Call(name, args.map(apply(state, _)), res)

      case Block(locals, progs) =>
        Block(locals, progs.map(apply(state, _)))

      case Choice(progs) =>
        Choice(progs.map(apply(state, _)))

      case If(test, left, right) =>
        If(apply(state, test), apply(state, left), apply(state, right))

      case While(test, body, attrs) =>
        While(apply(state, test), apply(state, body), attrs)

      case Iter(body, attrs) =>
        Iter(apply(state, body), attrs)

      case Ode(xs, rhs, dom, attrs) =>
        Ode(xs, rhs.map(apply(state, _)), apply(state, dom), attrs)

  // the replacement of a single application of an overloaded operator, whose arguments have been replaced already,
  // determined by the type of the arguments, which coincide for all overloaded operators,
  // where defined sorts are unfolded; the implementing functions are instantiated by matching their signature
  // against the unfolded types, e.g. seq.++ on Seq Int
  def resolve(state: State, app: App): Expr =
    val App(op, inst, typ, args) = app
    val inst_ = inst.map(Type.unfold(state, _))
    val fun_ = fun(op.name, op.arity, inst_.head)
    val su = Type.bind(fun_.args, inst_)
    App(fun_, inst_, su(fun_.res), args)
