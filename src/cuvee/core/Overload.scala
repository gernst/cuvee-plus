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
// and select and store, which index and update arrays, sequences, and maps;
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

  // the update m[k := v] of a map overwrites it by the singleton map
  val mapStore =
    val sig = Fun("store", List(a, Param.b), Fun.formals(Sort.map(a, Param.b), a, Param.b), Sort.map(a, Param.b))
    Impl(sig, { case (state, List(m, k, v)) => app(state, Fun.map.update, List(m, FinMaps.singleton(k, v))) })

  // membership x in s and the cardinality |s| of sequences, sets, and multisets, which the frontends build directly,
  // where membership is resolved by the type of its second argument (see dispatch)
  val member = Fun("in", List(a, Param.b), Fun.formals(a, Param.b), Sort.bool)
  val card = Fun("|_|", List(a), Fun.formals(a), Sort.int)

  // x in s for a sequence holds if s contains the sequence [x] of length 1, for a multiset if x occurs in it
  val seqMember =
    val sig = Fun("in", List(a), Fun.formals(a, Sort.seq(a)), Sort.bool)
    Impl(sig, { case (state, List(x, s)) => app(state, Fun.seq.contains, List(s, Seqs.unit(x))) })

  val bagMember =
    val sig = Fun("in", List(a), Fun.formals(a, Sort.bag(a)), Sort.bool)
    Impl(sig, { case (state, List(x, s)) => Lt.int(Zero.int, app(state, Fun.bag.count, List(x, s))) })

  // the multiplicity s[x] of an element of a multiset
  val bagSelect =
    val sig = Fun("select", List(a), Fun.formals(Sort.bag(a), a), Sort.int)
    Impl(sig, { case (state, List(s, x)) => app(state, Fun.bag.count, List(x, s)) })

  // proper prefixes, subsets, and submultisets s < t, which are different
  def proper(con: Con, fun: Fun) =
    val sig = Fun("<", List(a), Fun.formals(Sort(con, List(a)), Sort(con, List(a))), Sort.bool)
    Impl(sig, { case (state, List(s, t)) => And(app(state, fun, List(s, t)), Not(Eq(s, t))) })

  // the application of an implementation, whose signature is matched against the argument types,
  // in which defined sorts are expanded already (see Type.expand)
  def app(state: State, fun: Fun, args: List[Expr]): App =
    val inst = args.types
    val su = Type.bind(state, fun.args, inst)
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
      // negation is generic in Dafny, where it is also the complement of bitvectors
      (Name("not", None), 1, Con.bool) -> Impl(Fun.not),
      (Name("*", None), 2, Con.set) -> Impl(Fun.set.inter),
      (Name("*", None), 2, Con.bag) -> Impl(Fun.bag.inter),
      (Name("+", None), 2, Con.seq) -> Impl(Fun.seq.concat),
      (Name("+", None), 2, Con.set) -> Impl(Fun.set.union),
      (Name("+", None), 2, Con.bag) -> Impl(Fun.bag.union),
      (Name("+", None), 2, Con.map) -> Impl(Fun.map.update),
      (Name("-", None), 2, Con.set) -> Impl(Fun.set.minus),
      (Name("-", None), 2, Con.bag) -> Impl(Fun.bag.minus),
      (Name("-", None), 2, Con.map) -> Impl(Fun.map.minus),
      (Name("<", None), 2, Con.seq) -> proper(Con.seq, Fun.seq.prefixof),
      (Name("<", None), 2, Con.set) -> proper(Con.set, Fun.set.subset),
      (Name("<", None), 2, Con.bag) -> proper(Con.bag, Fun.bag.subbag),
      (Name("<=", None), 2, Con.seq) -> Impl(Fun.seq.prefixof),
      (Name("<=", None), 2, Con.set) -> Impl(Fun.set.subset),
      (Name("<=", None), 2, Con.bag) -> Impl(Fun.bag.subbag),
      // submaps, which are not strict, there is no < on maps
      (Name("<=", None), 2, Con.map) -> Impl(Fun.map.subset),
      (Name("div", None), 2, Con.real) -> Impl(Fun.real.div),
      (Name("in", None), 2, Con.seq) -> seqMember,
      (Name("in", None), 2, Con.set) -> Impl(Fun.set.member),
      (Name("in", None), 2, Con.bag) -> bagMember,
      (Name("in", None), 2, Con.map) -> Impl(Fun.map.member),
      (Name("select", None), 2, Con.array) -> Impl(Fun.select),
      (Name("select", None), 2, Con.seq) -> Impl(Fun.seq.nth),
      (Name("select", None), 2, Con.bag) -> bagSelect,
      (Name("select", None), 2, Con.map) -> Impl(Fun.map.get),
      (Name("store", None), 3, Con.array) -> Impl(Fun.store),
      (Name("store", None), 3, Con.seq) -> seqStore,
      (Name("store", None), 3, Con.map) -> mapStore,
      (Name("|_|", None), 1, Con.seq) -> Impl(Fun.seq.len),
      (Name("|_|", None), 1, Con.set) -> Impl(Fun.set.card),
      (Name("|_|", None), 1, Con.bag) -> Impl(Fun.bag.card),
      (Name("|_|", None), 1, Con.map) -> Impl(Fun.map.card)
    )

    Map(arith ++ other*)

  // the operators on bitvectors, as named by the frontends, by the functions of SMT-LIB for the width of the arguments,
  // where division, remainder, and the comparisons are unsigned, as in Dafny
  val bitvectors: Map[(Name, Int), String] =
    val ops = List(
      ("+", 2) -> "bvadd",
      ("-", 2) -> "bvsub",
      ("*", 2) -> "bvmul",
      ("div", 2) -> "bvudiv",
      ("mod", 2) -> "bvurem",
      ("-", 1) -> "bvneg",
      ("not", 1) -> "bvnot",
      ("&", 2) -> "bvand",
      ("^", 2) -> "bvxor",
      ("<", 2) -> "bvult",
      ("<=", 2) -> "bvule",
      (">", 2) -> "bvugt",
      (">=", 2) -> "bvuge"
    )
    for ((name, arity), fun) <- ops.toMap
    yield (Name(name, None), arity) -> fun

  // the conversions e as int and e as bv8 of the frontends, whose implementation depends on the target type as well
  val toInt = Name("as_int", None)
  val toBitVec = Name("as_bv", None)

  // the conversions of integers and bitvectors from the type `typ` to the type `res`, the identity on equal types;
  // bitvectors are extended by zeros or truncated to the lower bits
  def conversion(name: Name, typ: Type, res: Type): Option[Impl] =
    def id = Impl(Fun(name, Nil, Fun.formals(typ), res), { case (_, List(arg)) => arg })
    def impl(fun: Fun) = Impl(fun.copy(name = name), { case (state, List(arg)) => app(state, fun, List(arg)) })

    (name, typ, res) match
      case (`toInt`, Sort.int, Sort.int)               => Some(id)
      case (`toInt`, BitVec(n), Sort.int)              => BitVecs.fun("bv2nat", Nil, List(n)).map(impl)
      case (`toBitVec`, Sort.int, BitVec(m))           => Some(impl(BitVecs.int2bv(m)))
      case (`toBitVec`, BitVec(n), BitVec(m)) if n == m => Some(id)
      case (`toBitVec`, BitVec(n), BitVec(m)) if n < m  => BitVecs.fun("zero_extend", List(m - n), List(n)).map(impl)
      case (`toBitVec`, BitVec(n), BitVec(m))           => BitVecs.fun("extract", List(m - 1, 0), List(n)).map(impl)
      case _                                            => None

  // the position of the argument whose type determines the implementation, the first one except for membership
  def dispatch(name: Name, arity: Int): Int =
    if name == member.name && arity == 2 then 1 else 0

  // the overloaded operators (name and arity)
  val generic: Set[(Name, Int)] =
    val ops =
      for (name, arity, _) <- table.keySet
      yield (name, arity)
    ops ++ bitvectors.keySet + (toInt -> 1) + (toBitVec -> 1)

  // the implementation of operator `name` with `arity` for a first argument of type `typ` and the result type `res`,
  // which only the conversions depend on, if any, where `typ` must be unfolded already;
  // the functions on bitvectors are those of the width of `typ`, whose signatures carry the name of the operator,
  // such that the type checker can match them against the application
  def impl(name: Name, arity: Int, typ: Type, res: Type): Option[Impl] =
    typ match
      case _ if name == toInt || name == toBitVec =>
        conversion(name, typ, res)

      case BitVec(n) =>
        for
          op <- bitvectors.get((name, arity))
          fun <- BitVecs.fun(op, Nil, List.fill(arity)(n))
        yield Impl(fun.copy(name = name), (state, args) => app(state, fun, args))

      case Sort(con, _) =>
        table.get((name, arity, con))

      case _ =>
        None

  // whether `fun` is the generic declaration of an overloaded operator in a prelude,
  // the implementations have no type parameters or are not generic in the type of the first argument
  def isGeneric(fun: Fun): Boolean =
    fun.params.nonEmpty && generic.contains((fun.name, fun.arity)) && fun.args(dispatch(fun.name, fun.arity)).isInstanceOf[Param]

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
  // by its implementation for the type of the first argument, in which defined sorts are expanded already
  def resolve(state: State, app: App): Expr =
    val App(op, inst, typ, args) = app
    val typ_ = args(dispatch(op.name, op.arity)).typ

    impl(op.name, op.arity, typ_, typ) match
      case Some(Impl(_, build)) => build(state, args)
      case None                 => Error.raise("operator not defined for type", op.name, typ_)
