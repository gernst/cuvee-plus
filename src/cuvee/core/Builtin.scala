package cuvee.core

import util.Name
import util.Rational
import cuvee.Error

object True extends App(Fun.true_, Nil, Sort.bool, Nil)
object False extends App(Fun.false_, Nil, Sort.bool, Nil)

object Skip extends Block(Nil, Nil)

object Send extends Sugar.call("history_send", 3, 1)
object Recv extends Sugar.call("history_receive", 2, 2)
object Tick extends Sugar.call("history_tick", 2, 1)

object Eq extends Sugar.binary(Fun.eq_):
  def apply(left: List[Expr], right: List[Expr]): List[Expr] =
    Error.report("invalid equation between mismatching arguments", left, right):
      require(left.length == right.length)

    for (a, b) <- left zip right
    yield Eq(a, b)

object Ite extends Sugar.ternary(Fun.ite)

object Select extends Sugar.binary(Fun.select):
  def apply(base: Expr, indices: List[Expr]): Expr =
    indices.foldLeft(base)(this)

object Store extends Sugar.ternary(Fun.store):
  // Note: most significant update first
  def flatten(expr: Expr): (Expr, List[(Expr, Expr)]) =
    expr match
      case Store(inner, index, value) =>
        val (base, pairs) = flatten(inner)
        (base, (index, value) :: pairs)

      case _ =>
        (expr, Nil)

object Not extends Sugar.unary(Fun.not):
  def apply(args: List[Expr]): List[Expr] =
    args map this

object Imp extends Sugar.binary(Fun.imp)
object Eqv extends Sugar.binary(Fun.eqv)
object And extends Sugar.commutative(Fun.and, True, Assoc.Left)
object Or extends Sugar.commutative(Fun.or, False, Assoc.Left)

object Ints:
  val zero = Lit(BigInt(0), Sort.int)
  val one = Lit(BigInt(1), Sort.int)

  object num extends Sugar.lit(Sort.int)
  object uminus extends Sugar.unary(Fun.int.uminus)
  object plus extends Sugar.commutative(Fun.int.plus, zero, Assoc.Left)
  object minus extends Sugar.associative(Fun.int.minus, Assoc.Left)
  object times extends Sugar.commutative(Fun.int.times, one, Assoc.Left)
  object div extends Sugar.binary(Fun.int.div)
  object mod extends Sugar.binary(Fun.int.mod)

  object lt extends Sugar.binary(Fun.int.lt)
  object le extends Sugar.binary(Fun.int.le)
  object gt extends Sugar.binary(Fun.int.gt)
  object ge extends Sugar.binary(Fun.int.ge)

  object succ:
    def apply(expr: Expr) =
      plus(expr, one)

    def unapply(expr: Expr) =
      expr match
        case plus(args) if args.contains(one) => Some(plus(args diff List(one)))
        case _                                => None

  lazy val ring =
    Ring(Sort.int, zero, num, uminus, plus, minus, times, n => Lit(n.toBigInt, Sort.int))

object Reals:
  val zero = Lit(Rational(0), Sort.real)
  val one = Lit(Rational(1), Sort.real)

  object num extends Sugar.lit(Sort.real)
  object uminus extends Sugar.unary(Fun.real.uminus)
  object plus extends Sugar.commutative(Fun.real.plus, zero, Assoc.Left)
  object minus extends Sugar.associative(Fun.real.minus, Assoc.Left)
  object times extends Sugar.commutative(Fun.real.times, one, Assoc.Left)
  object div extends Sugar.binary(Fun.real.div)

  object lt extends Sugar.binary(Fun.real.lt)
  object le extends Sugar.binary(Fun.real.le)
  object gt extends Sugar.binary(Fun.real.gt)
  object ge extends Sugar.binary(Fun.real.ge)

  lazy val ring =
    Ring(Sort.real, zero, num, uminus, plus, minus, times, r => Lit(r, Sort.real))

case class Ring(
    typ: Type,
    zero: Expr,
    num: Sugar.lit,
    uminus: Sugar.unary,
    plus: Sugar.commutative,
    minus: Sugar.associative,
    times: Sugar.commutative,
    lit: Rational => Expr
)

object Ring:
  def apply(typ: Type): Option[Ring] =
    typ match
      case Sort.int  => Some(Ints.ring)
      case Sort.real => Some(Reals.ring)
      case _         => None

object Counter extends Sugar.ternary(Fun.trace.counter)
object Current extends Sugar.unary(Fun.trace.current)
object Butlast extends Sugar.unary(Fun.trace.butlast)
object Earlier extends Sugar.binary(Fun.trace.earlier)

object Lists:
  object nil:
    def apply(elem: Type): Expr =
      App(Fun.list.nil, Nil, Sort.list(elem), Nil)

    def unapply(expr: Expr): Boolean =
      expr match
        case App(fun, _, _, Nil) => fun == Fun.list.nil
        case _                   => false

  object cons extends Sugar.binary(Fun.list.cons)

object Traces:
  object stop extends Sugar.unary(Fun.trace.stop)
  object step extends Sugar.binary(Fun.trace.step)

object Unspecified:
  def apply(typ: Type): Expr =
    App(Fun.trace.unspecified, Nil, typ, Nil)

  def unapply(expr: Expr): Option[Type] =
    expr match
      case App(fun, _, typ, Nil) if fun == Fun.trace.unspecified => Some(typ)
      case _                                                     => None

object Tuples:
  def name(arity: Int) =
    Name("tuple", Some(arity))

  def unapply(expr: Expr): Option[List[Expr]] =
    expr match
      case App(fun, _, _, args) if fun.name == name(args.length) => Some(args)
      case _                                                     => None

object Seqs:
  object empty:
    def apply(elem: Type): Expr =
      App(Fun.seq.empty, Nil, Sort.seq(elem), Nil)

    def unapply(expr: Expr): Boolean =
      expr match
        case App(fun, _, _, Nil) => fun == Fun.seq.empty
        case _                   => false

  object unit extends Sugar.unary(Fun.seq.unit)
  object concat extends Sugar.associative(Fun.seq.concat, Assoc.Left)
  object len extends Sugar.unary(Fun.seq.len)
  object nth extends Sugar.binary(Fun.seq.nth)
  object update extends Sugar.ternary(Fun.seq.update)
  object extract extends Sugar.ternary(Fun.seq.extract)
  object contains extends Sugar.binary(Fun.seq.contains)
  object prefixof extends Sugar.binary(Fun.seq.prefixof)
  object store extends Sugar.ternary(Fun.seq.store)
  object snoc extends Sugar.binary(Fun.seq.snoc)
  object slice extends Sugar.ternary(Fun.seq.slice)
  object member extends Sugar.binary(Fun.seq.member)
  object proper extends Sugar.binary(Fun.seq.proper)

object Sets:
  object empty:
    def apply(elem: Type): Expr =
      App(Fun.set.empty, Nil, Sort.set(elem), Nil)

    def unapply(expr: Expr): Boolean =
      expr match
        case App(fun, _, _, Nil) => fun == Fun.set.empty
        case _                   => false

  object singleton extends Sugar.unary(Fun.set.singleton)
  object update extends Sugar.ternary(Fun.set.update)
  object union extends Sugar.associative(Fun.set.union, Assoc.Left)
  object inter extends Sugar.associative(Fun.set.inter, Assoc.Left)
  object minus extends Sugar.binary(Fun.set.minus)
  object member extends Sugar.binary(Fun.set.member)
  object subset extends Sugar.binary(Fun.set.subset)
  object card extends Sugar.unary(Fun.set.card)
  object proper extends Sugar.binary(Fun.set.proper)

object Bags:
  object empty:
    def apply(elem: Type): Expr =
      App(Fun.bag.empty, Nil, Sort.bag(elem), Nil)

    def unapply(expr: Expr): Boolean =
      expr match
        case App(fun, _, _, Nil) => fun == Fun.bag.empty
        case _                   => false

  object make extends Sugar.binary(Fun.bag.make)
  object union extends Sugar.associative(Fun.bag.union, Assoc.Left)
  object inter extends Sugar.associative(Fun.bag.inter, Assoc.Left)
  object minus extends Sugar.binary(Fun.bag.minus)
  object count extends Sugar.binary(Fun.bag.count)
  object subbag extends Sugar.binary(Fun.bag.subbag)
  object card extends Sugar.unary(Fun.bag.card)
  object member extends Sugar.binary(Fun.bag.member)
  object select extends Sugar.binary(Fun.bag.select)
  object store extends Sugar.ternary(Fun.bag.store)
  object insert extends Sugar.binary(Fun.bag.insert)
  object proper extends Sugar.binary(Fun.bag.proper)

object FinMaps:
  object empty:
    def apply(key: Type, value: Type): Expr =
      App(Fun.map.empty, Nil, Sort.map(key, value), Nil)

    def unapply(expr: Expr): Boolean =
      expr match
        case App(fun, _, _, Nil) => fun == Fun.map.empty
        case _                   => false

  object singleton extends Sugar.binary(Fun.map.singleton)
  object card extends Sugar.unary(Fun.map.card)
  object member extends Sugar.binary(Fun.map.member)
  object keys extends Sugar.unary(Fun.map.keys)
  object values extends Sugar.unary(Fun.map.values)
  object subset extends Sugar.binary(Fun.map.subset)
  object get extends Sugar.binary(Fun.map.get)
  object update extends Sugar.associative(Fun.map.update, Assoc.Left)
  object minus extends Sugar.binary(Fun.map.minus)
  object store extends Sugar.ternary(Fun.map.store)

// the functions on bitvectors of SMT-LIB, which are instantiated for the widths of their arguments,
// where indexed functions are named by their indexed identifier, e.g. "_ extract 7 0" for (_ extract 7 0)
object BitVecs:
  val unary = Set("bvnot", "bvneg")
  val binary = Set(
    "bvand",
    "bvor",
    "bvxor",
    "bvnand",
    "bvnor",
    "bvxnor",
    "bvadd",
    "bvsub",
    "bvmul",
    "bvudiv",
    "bvurem",
    "bvsdiv",
    "bvsrem",
    "bvsmod",
    "bvshl",
    "bvlshr",
    "bvashr"
  )
  val comparisons = Set("bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge")
  val indexed = Set("extract", "zero_extend", "sign_extend", "repeat", "rotate_left", "rotate_right")

  // the functions that are not indexed
  val names = unary ++ binary ++ comparisons + "bvcomp" + "concat" + "bv2nat"

  // the conversion of an integer to a bitvector of width n, modulo 2^n,
  // the converse is bv2nat (see fun), the natural number that a bitvector represents
  def int2bv(n: Int): Fun =
    Fun("_ int2bv " + n, Nil, Fun.formals(Sort.int), BitVec(n))

  // the instance of the function `name` with `indices` for arguments of the widths `widths`, if it exists
  def fun(name: String, indices: List[Int], widths: List[Int]): Option[Fun] =
    def instance(res: Type) =
      val name_ = if indices.isEmpty then name else ("_" :: name :: indices.map(_.toString)).mkString(" ")
      Some(Fun(name_, Nil, Fun.formals(widths.map(BitVec(_))*), res))

    (name, indices, widths) match
      case (_, Nil, List(n)) if unary contains name                      => instance(BitVec(n))
      case (_, Nil, List(n, m)) if (binary contains name) && n == m      => instance(BitVec(n))
      case (_, Nil, List(n, m)) if (comparisons contains name) && n == m => instance(Sort.bool)
      case ("bvcomp", Nil, List(n, m)) if n == m                         => instance(BitVec(1))
      case ("bv2nat", Nil, List(n))                                      => instance(Sort.int)
      case ("concat", Nil, List(n, m))                                   => instance(BitVec(n + m))
      case ("extract", List(i, j), List(n)) if j <= i && i < n           => instance(BitVec(i - j + 1))
      case ("zero_extend" | "sign_extend", List(k), List(n))             => instance(BitVec(n + k))
      case ("repeat", List(k), List(n)) if 0 < k                         => instance(BitVec(n * k))
      case ("rotate_left" | "rotate_right", List(k), List(n))            => instance(BitVec(n))
      case _                                                             => None

  // the bitvector literal of width n with `value`, between 0 and 2^n - 1
  def lit(value: BigInt, n: Int): Lit =
    Lit(value, BitVec(n))
