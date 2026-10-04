package cuvee.core

import util.Name
import cuvee.Error

// an implementation of an overloaded operator for one sort constructor of its first argument:
// its signature, against which the application is type checked, and the expression that replaces the application
case class Impl(sig: Fun, build: (State, List[Expr]) => Expr)

object Impl:
  // the application of a function with the same signature
  def apply(fun: Fun): Impl =
    Impl(fun, (state, args) => Overload.app(state, fun, args))

// overloaded operators, which are implemented by different functions depending on the type of the first argument:
// arithmetic and comparisons on Int and Real, e.g. + by Fun.int.plus on Int and by Fun.real.plus on Real,
// + and <= on sequences, which are concatenation and prefix,
// and select and store, which index and update arrays and sequences;
// the frontends declare them generically in their preludes, the type checker determines the implementation
// once the type of the first argument is known and checks the application against its signature (see Type.check),
// and afterwards, each application is replaced by its implementation (see apply),
// such that the generic operators never leave the frontend
object Overload:
  import Param.a

  // the update s[i := v] of a sequence replaces the subsequence of length 1 at index i
  val seqStore =
    val sig = Fun("store", List(a), Fun.formals(Sort.seq(a), Sort.int, a), Sort.seq(a))
    Impl(sig, { case (state, List(s, i, v)) => app(state, Fun.seq.update, List(s, i, App(Fun.seq.unit, List(v)))) })

  // the application of an implementation, whose signature is matched against the argument types,
  // where defined sorts are unfolded
  def app(state: State, fun: Fun, args: List[Expr]): App =
    val inst = args.map(arg => Type.unfold(state, arg.typ))
    val su = Type.bind(fun.args, inst)
    App(fun, inst, su(fun.res), args)

  // the implementation of each operator (name and arity) for the sort constructor of its first argument,
  // named as in SMT-LIB, where div and mod are on Int only and / on Real only,
  // except that div on Real is real division, since Dafny's / translates to div on both types
  val table: Map[(Name, Int, Con), Impl] =
    val arith =
      for fun <- Fun.int.all ++ Fun.real.all
      yield
        val Sort(con, _) = fun.args.head: @unchecked
        (fun.name, fun.arity, con) -> Impl(fun)

    val other = List(
      (Name("div", None), 2, Con.real) -> Impl(Fun.real.div),
      (Name("+", None), 2, Con.seq) -> Impl(Fun.seq.concat),
      (Name("<=", None), 2, Con.seq) -> Impl(Fun.seq.prefixof),
      (Name("select", None), 2, Con.array) -> Impl(Fun.select),
      (Name("store", None), 3, Con.array) -> Impl(Fun.store),
      (Name("select", None), 2, Con.seq) -> Impl(Fun.seq.nth),
      (Name("store", None), 3, Con.seq) -> seqStore
    )

    Map(arith ++ other*)

  // the overloaded operators (name and arity)
  val generic: Set[(Name, Int)] =
    for (name, arity, _) <- table.keySet
    yield (name, arity)

  // the implementation of operator `name` with `arity` for a first argument of type `typ`, if any,
  // where `typ` must be unfolded already
  def impl(name: Name, arity: Int, typ: Type): Option[Impl] =
    typ match
      case Sort(con, _) => table.get((name, arity, con))
      case _: Param     => None

  // whether `fun` is the generic declaration of an overloaded operator in a prelude,
  // the implementations have no type parameters or are not generic in the type of the first argument
  def isGeneric(fun: Fun): Boolean =
    fun.params.nonEmpty && generic.contains((fun.name, fun.arity)) && fun.args.head.isInstanceOf[Param]

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

      case Old(expr) =>
        Old(apply(state, expr))

      case Trace(init, deps, acc, bound, update) =>
        Trace(apply(state, init), deps.map(apply(state, _)), acc, bound, update.map((g, e) => (apply(state, g), apply(state, e))))

      case Maps(deps, bound, update) =>
        Maps(deps.map(apply(state, _)), bound, update.map((g, e) => (apply(state, g), apply(state, e))))

      case Invs(deps, bound, body) =>
        Invs(deps.map(apply(state, _)), bound, apply(state, body))

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

      case Par(calls) =>
        Par(for Call(proc, args, res) <- calls yield Call(proc, args.map(apply(state, _)), res))

  // the replacement of a single application of an overloaded operator, whose arguments have been replaced already,
  // by its implementation for the type of the first argument, where defined sorts are unfolded
  def resolve(state: State, app: App): Expr =
    val App(op, inst, typ, args) = app
    val typ_ = Type.unfold(state, args.head.typ)

    impl(op.name, op.arity, typ_) match
      case Some(Impl(_, build)) => build(state, args)
      case None                 => Error.raise("operator not defined for type", op.name, typ_)
