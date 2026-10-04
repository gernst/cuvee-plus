package cuvee.core

import util.Rational
import cuvee.Error

// constants and arithmetic per type, e.g. Plus.int and Plus.real,
// where DivBy.int is div and DivBy.real is /, and Mod is on Int only
object Zero:
  val int = Lit(BigInt(0), Sort.int)
  val real = Lit(Rational(0), Sort.real)

object One:
  val int = Lit(BigInt(1), Sort.int)
  val real = Lit(Rational(1), Sort.real)

object True extends App(Fun.true_, Nil, Sort.bool, Nil)
object False extends App(Fun.false_, Nil, Sort.bool, Nil)

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

object UMinus:
  object int extends Sugar.unary(Fun.int.uminus)
  object real extends Sugar.unary(Fun.real.uminus)

object Plus:
  object int extends Sugar.commutative(Fun.int.plus, Zero.int, Assoc.Left)
  object real extends Sugar.commutative(Fun.real.plus, Zero.real, Assoc.Left)

object Minus:
  object int extends Sugar.associative(Fun.int.minus, Assoc.Left)
  object real extends Sugar.associative(Fun.real.minus, Assoc.Left)

object Times:
  object int extends Sugar.commutative(Fun.int.times, One.int, Assoc.Left)
  object real extends Sugar.commutative(Fun.real.times, One.real, Assoc.Left)

object DivBy:
  object int extends Sugar.associative(Fun.int.div, Assoc.Left)
  object real extends Sugar.associative(Fun.real.div, Assoc.Left)

// mod is not associative, and unlike div not n-ary in SMT-LIB
object Mod:
  object int extends Sugar.binary(Fun.int.mod)

object Succ:
  def apply(expr: Expr) =
    Plus.int(expr, One.int)

  def unapply(expr: Expr) =
    expr match
      case Plus.int(List(arg, One.int)) => Some(arg)
      case Plus.int(List(One.int, arg)) => Some(arg)
      case _                            => None

object Lt:
  object int extends Sugar.binary(Fun.int.lt)
  object real extends Sugar.binary(Fun.real.lt)

object Le:
  object int extends Sugar.binary(Fun.int.le)
  object real extends Sugar.binary(Fun.real.le)

object Gt:
  object int extends Sugar.binary(Fun.int.gt)
  object real extends Sugar.binary(Fun.real.gt)

object Ge:
  object int extends Sugar.binary(Fun.int.ge)
  object real extends Sugar.binary(Fun.real.ge)

// the functions on traces (see Fun.trace): counter(i, c, n) is the trace i, i + c, ..., i + n c,
// and butlast(X), written ⌊X⌋, is the sequence of all but the last element of X
object Counter extends Sugar.ternary(Fun.trace.counter)
object Butlast extends Sugar.unary(Fun.trace.butlast)

// the functions on sequences, as in Fun.seq, e.g. Seqs.len(s) and Seqs.nth(s, i)
object Seqs:
  // the empty sequence needs the type of its elements
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
