package cuvee.core

import cuvee.Error

object Zero extends Lit(BigInt(0), Sort.int)
object One extends Lit(BigInt(1), Sort.int)

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
object And extends Sugar.commutative(Fun.and, True, Assoc.Left)
object Or extends Sugar.commutative(Fun.or, False, Assoc.Left)

object UMinus extends Sugar.unary(Fun.uminus)
object Plus extends Sugar.commutative(Fun.plus, Zero, Assoc.Left)
object Minus extends Sugar.associative(Fun.minus, Assoc.Left)
object Times extends Sugar.commutative(Fun.times, One, Assoc.Left)
object DivBy extends Sugar.associative(Fun.div, Assoc.Left)
object Mod extends Sugar.associative(Fun.mod, Assoc.Left)

object Succ:
  def apply(expr: Expr) =
    Plus(expr, One)

  def unapply(expr: Expr) =
    expr match
      case Plus(List(arg, One)) => Some(arg)
      case Plus(List(One, arg)) => Some(arg)
      case _                    => None

object Lt extends Sugar.binary(Fun.lt)
object Le extends Sugar.binary(Fun.le)
object Gt extends Sugar.binary(Fun.gt)
object Ge extends Sugar.binary(Fun.ge)
