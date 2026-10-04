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
    Impl(sig, { case (state, List(s, i, v)) => app(state, Fun.seq.update, List(s, i, Seqs.unit(v))) })

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
    expr.map(apply(state, _)) match
      case app_ @ App(fun, _, _, _) if isGeneric(fun) =>
        resolve(state, app_)

      case expr_ =>
        expr_

  // replace all overloaded operators in the expressions of a type checked program, including its attributes
  def apply(state: State, prog: Prog): Prog =
    prog.map(apply(state, _: Expr), apply(state, _: Prog))

  // the replacement of a single application of an overloaded operator, whose arguments have been replaced already,
  // by its implementation for the type of the first argument, where defined sorts are unfolded
  def resolve(state: State, app: App): Expr =
    val App(op, inst, typ, args) = app
    val typ_ = Type.unfold(state, args.head.typ)

    impl(op.name, op.arity, typ_) match
      case Some(Impl(_, build)) => build(state, args)
      case None                 => Error.raise("operator not defined for type", op.name, typ_)
