package cuvee.core

import util.Name
import cuvee.Error

// overloaded operators, which are implemented by different functions depending on the type of the first argument:
// arithmetic and comparisons on Int and Real, e.g. + by Fun.int.plus on Int and by Fun.real.plus on Real,
// + and <= on sequences, which are concatenation and prefix,
// and select and store, which index and update arrays, sequences, and maps;
// the frontends declare them generically in their preludes, the type checker determines the implementation
// once the type of the first argument is known and checks the application against its signature (see Type.check),
// and afterwards, each application is replaced by its implementation (see apply),
// such that the generic operators never leave the frontend;
// the implementations are grouped by sort constructor like the functions (see Fun), each a pair of
// the signature, which carries the name of the operator as in Dafny after translation (see dafny.Grammar.translate),
// e.g. + for the concatenation of sequences, and select and store for indexing and updates s[i] and s[i := v],
// against which the application is type checked, and the function that replaces the application
object Overload:
  import Param.a
  import Param.b

  // the implementation of operator `op` by `fun`, whose signature is that of `fun`
  def overload(op: Name, fun: Fun): (Fun, Fun) =
    (fun.copy(name = op), fun)

  // membership x in s and the cardinality |s| of sequences, sets, multisets, and maps, which the frontends build directly,
  // where membership is resolved by the type of its second argument (see dispatch)
  val member = Fun("in", List(a, b), Fun.formals(a, b), Sort.bool)
  val card = Fun("|_|", List(a), Fun.formals(a), Sort.int)

  // negation is generic in Dafny, where it is also the complement of bitvectors
  object bool:
    val not = overload("not", Fun.not)

    val all = List(not)

  // arithmetic and comparisons, named as in SMT-LIB, where div and mod are on Int only
  object int:
    val uminus = overload("-", Fun.int.uminus)
    val plus = overload("+", Fun.int.plus)
    val minus = overload("-", Fun.int.minus)
    val times = overload("*", Fun.int.times)
    val div = overload("div", Fun.int.div)
    val mod = overload("mod", Fun.int.mod)
    val lt = overload("<", Fun.int.lt)
    val le = overload("<=", Fun.int.le)
    val gt = overload(">", Fun.int.gt)
    val ge = overload(">=", Fun.int.ge)

    val all = List(uminus, plus, minus, times, div, mod, lt, le, gt, ge)

  // / is real division, as is div, since Dafny's / translates to div on both types
  object real:
    val uminus = overload("-", Fun.real.uminus)
    val plus = overload("+", Fun.real.plus)
    val minus = overload("-", Fun.real.minus)
    val times = overload("*", Fun.real.times)
    val div = overload("/", Fun.real.div)
    val div_ = overload("div", Fun.real.div)
    val lt = overload("<", Fun.real.lt)
    val le = overload("<=", Fun.real.le)
    val gt = overload(">", Fun.real.gt)
    val ge = overload(">=", Fun.real.ge)

    val all = List(uminus, plus, minus, times, div, div_, lt, le, gt, ge)

  object array:
    val select = overload("select", Fun.select)
    val store = overload("store", Fun.store)

    val all = List(select, store)

  object seq:
    val concat = overload("+", Fun.seq.concat)
    val prefix = overload("<=", Fun.seq.prefixof)
    val proper = overload("<", Fun.seq.proper)
    val member = overload("in", Fun.seq.member)
    val select = overload("select", Fun.seq.nth)
    val store = overload("store", Fun.seq.store)
    val card = overload("|_|", Fun.seq.len)

    val all = List(concat, prefix, proper, member, select, store, card)

  object set:
    val inter = overload("*", Fun.set.inter)
    val union = overload("+", Fun.set.union)
    val minus = overload("-", Fun.set.minus)
    val subset = overload("<=", Fun.set.subset)
    val proper = overload("<", Fun.set.proper)
    val member = overload("in", Fun.set.member)
    val card = overload("|_|", Fun.set.card)

    val all = List(inter, union, minus, subset, proper, member, card)

  object bag:
    val inter = overload("*", Fun.bag.inter)
    val union = overload("+", Fun.bag.union)
    val minus = overload("-", Fun.bag.minus)
    val subbag = overload("<=", Fun.bag.subbag)
    val proper = overload("<", Fun.bag.proper)
    val member = overload("in", Fun.bag.member)
    val select = overload("select", Fun.bag.select)
    val card = overload("|_|", Fun.bag.card)

    val all = List(inter, union, minus, subbag, proper, member, select, card)

  // submaps are not strict, there is no < on maps
  object map:
    val update = overload("+", Fun.map.update)
    val minus = overload("-", Fun.map.minus)
    val subset = overload("<=", Fun.map.subset)
    val member = overload("in", Fun.map.member)
    val select = overload("select", Fun.map.get)
    val store = overload("store", Fun.map.store)
    val card = overload("|_|", Fun.map.card)

    val all = List(update, minus, subset, member, select, store, card)

  // the application of an implementation, whose signature is matched against the argument types,
  // in which defined sorts are expanded already (see Type.expand)
  def app(state: State, fun: Fun, args: List[Expr]): App =
    val inst = args.types
    val su = Type.bind(state, fun.args, inst)
    App(fun, inst, su(fun.res), args)

  // the implementation of each operator (name and arity) for the sort constructor of the argument that determines it,
  // by its signature
  val table: Map[(Name, Int, Con), (Fun, Fun)] =
    val impls = bool.all ++ int.all ++ real.all ++ array.all ++ seq.all ++ set.all ++ bag.all ++ map.all
    val entries =
      for (sig, fun) <- impls
      yield
        val Sort(con, _) = sig.args(dispatch(sig.name, sig.arity)): @unchecked
        (sig.name, sig.arity, con) -> (sig, fun)

    Error.report("ambiguous implementations of overloaded operators", entries.map(_._1).diff(entries.map(_._1).distinct)):
      require(entries.map(_._1).distinct.length == entries.length)

    entries.toMap

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
  // where the identity is implemented by the conversion itself (see resolve)
  def conversion(name: Name, typ: Type, res: Type): Option[(Fun, Fun)] =
    def id = overload(name, Fun(name, Nil, Fun.formals(typ), res))

    (name, typ, res) match
      case (`toInt`, Sort.int, Sort.int)               => Some(id)
      case (`toInt`, BitVec(n), Sort.int)              => BitVecs.fun("bv2nat", Nil, List(n)).map(overload(name, _))
      case (`toBitVec`, Sort.int, BitVec(m))           => Some(overload(name, BitVecs.int2bv(m)))
      case (`toBitVec`, BitVec(n), BitVec(m)) if n == m => Some(id)
      case (`toBitVec`, BitVec(n), BitVec(m)) if n < m  => BitVecs.fun("zero_extend", List(m - n), List(n)).map(overload(name, _))
      case (`toBitVec`, BitVec(n), BitVec(m))           => BitVecs.fun("extract", List(m - 1, 0), List(n)).map(overload(name, _))
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
  def impl(name: Name, arity: Int, typ: Type, res: Type): Option[(Fun, Fun)] =
    typ match
      case _ if name == toInt || name == toBitVec =>
        conversion(name, typ, res)

      case BitVec(n) =>
        for
          op <- bitvectors.get((name, arity))
          fun <- BitVecs.fun(op, Nil, List.fill(arity)(n))
        yield overload(name, fun)

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
      case Some((_, fun)) if fun.name == toInt || fun.name == toBitVec => args.head
      case Some((_, fun))                                               => Overload.app(state, fun, args)
      case None                                                         => Error.raise("operator not defined for type", op.name, typ_)
