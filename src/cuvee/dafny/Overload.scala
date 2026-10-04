package cuvee.dafny

import util.Name
import cuvee.Error
import cuvee.core._

// Dafny overloads operators, e.g. + on int, seq, and set, which are declared once polymorphically in the prelude;
// after type checking, each application of such an operator is replaced by the function for the instantiated type,
// e.g. + on int by the builtin Fun.int.plus, such that the generic operators never leave the Dafny frontend
object Overload:
  // the function that implements an operator (name and arity) for arguments whose type has the given constructor,
  // where unary + is the identity, which is represented by None;
  // the operators are named as after Grammar.translate, e.g. / is div
  val table: Map[(Name, Int, Con), Option[Fun]] =
    def op(name: String, arity: Int, con: Con) =
      (Name(name, None), arity, con)

    Map(
      op("+", 1, Con.int) -> None,
      op("-", 1, Con.int) -> Some(Fun.int.uminus),
      op("+", 2, Con.int) -> Some(Fun.int.plus),
      op("-", 2, Con.int) -> Some(Fun.int.minus),
      op("*", 2, Con.int) -> Some(Fun.int.times),
      op("div", 2, Con.int) -> Some(Fun.int.div),
      op("mod", 2, Con.int) -> Some(Fun.int.mod),
      op("<", 2, Con.int) -> Some(Fun.int.lt),
      op("<=", 2, Con.int) -> Some(Fun.int.le),
      op(">", 2, Con.int) -> Some(Fun.int.gt),
      op(">=", 2, Con.int) -> Some(Fun.int.ge),
      op("+", 1, Con.real) -> None,
      op("-", 1, Con.real) -> Some(Fun.real.uminus),
      op("+", 2, Con.real) -> Some(Fun.real.plus),
      op("-", 2, Con.real) -> Some(Fun.real.minus),
      op("*", 2, Con.real) -> Some(Fun.real.times),
      op("div", 2, Con.real) -> Some(Fun.real.div),
      op("<", 2, Con.real) -> Some(Fun.real.lt),
      op("<=", 2, Con.real) -> Some(Fun.real.le),
      op(">", 2, Con.real) -> Some(Fun.real.gt),
      op(">=", 2, Con.real) -> Some(Fun.real.ge)
    )

  // the overloaded operators (name and arity)
  val generic: Set[(Name, Int)] =
    for (name, arity, _) <- table.keySet
    yield (name, arity)

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
  // the attributes of loops are checked and resolved separately by the parser
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
  // determined by the type of the arguments, which coincide for all overloaded operators;
  // raises an error if the operator is not defined for that type, e.g. for a type parameter
  def resolve(state: State, app: App): Expr =
    val App(fun, inst, typ, args) = app

    val key = inst.head match
      case Sort(con, _) => Some((fun.name, fun.arity, con))
      case _: Param     => None

    key.flatMap(table.get) match
      case Some(Some(fun_)) =>
        App(fun_, args)

      case Some(None) =>
        args.head

      case None =>
        Error.raise("operator not defined for type", fun.name, inst.head)
