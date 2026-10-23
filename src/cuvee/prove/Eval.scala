package cuvee.prove

import cuvee.core.*

// the values of closed terms of the functions that are computed from literals, for the counterexample search of
// Prove: an instance of a goal at literal values is evaluated directly, without the rules, the classes and the
// simplex, which may decide anything in a context whose contradiction they do not detect (e.g. the premise
// natural(4294967296) == zero of a case that the instance does not satisfy); integers and naturals are BigInt, the
// value of a natural is nonnegative; a term without a value (a variable, a division by zero, another function) has none
object Eval:
  // the functions whose values are computed from literals, without quantifiers
  val computed = Set("and", "or", "not", "=>", "=", "distinct", "<", "<=", ">", ">=", "+", "-", "*", "div", "mod", "ite", "true", "false", "integer", "natural", "zero", "succ")

  def evaluable(expr: Expr): Boolean =
    expr match
      case _: Var | _: Lit           => true
      case App(fun, _, _, args)      => computed.contains(fun.name.name) && args.forall(evaluable)
      case _                         => false

  def apply(expr: Expr): Option[BigInt | Boolean] =
    expr match
      case Lit(value: BigInt, _) =>
        Some(value)

      case App(fun, _, _, args) =>
        (fun.name.name, args) match
          case ("true", Nil)        => Some(true)
          case ("false", Nil)       => Some(false)
          case ("zero", Nil)        => Some(BigInt(0))
          case ("succ", List(n))    => int(n).map(_ + 1)
          case ("natural", List(x)) => int(x).map(_ max 0)
          case ("integer", List(n)) => int(n)
          case ("not", List(phi))   => bool(phi).map(!_)

          // a false conjunct decides the conjunction, also if another one has no value, and dually
          case ("and", phis) =>
            val values = phis.map(bool)
            if values.contains(Some(false)) then Some(false) else if values.forall(_.isDefined) then Some(true) else None

          case ("or", phis) =>
            val values = phis.map(bool)
            if values.contains(Some(true)) then Some(true) else if values.forall(_.isDefined) then Some(false) else None

          // right-associative: the premises together imply the conclusion
          case ("=>", phis) if phis.nonEmpty =>
            val premises = phis.init.map(bool)
            if premises.contains(Some(false)) then Some(true)
            else bool(phis.last) match
              case Some(true)                                  => Some(true)
              case Some(false) if premises.forall(_.isDefined) => Some(false)
              case _                                           => None

          case ("ite", List(test, left, right)) =>
            bool(test).flatMap(if _ then apply(left) else apply(right))

          case ("=", exprs) =>
            values(exprs).map(_.distinct.length == 1)

          case ("distinct", exprs) =>
            values(exprs).map(vs => vs.distinct.length == vs.length)

          case ("<" | "<=" | ">" | ">=", exprs) =>
            ints(exprs).map(vs => vs.zip(vs.tail).forall((a, b) => compare(fun.name.name, a, b)))

          case ("+", exprs) =>
            ints(exprs).map(_.sum)

          case ("*", exprs) =>
            ints(exprs).map(_.product)

          case ("-", List(arg)) =>
            int(arg).map(-_)

          case ("-", first :: rest) =>
            ints(first :: rest).map(vs => vs.head - vs.tail.sum)

          case ("div", List(a, b)) =>
            ints(List(a, b)).collect { case List(a, b) if b != 0 => euclidean(a, b)._1 }

          case ("mod", List(a, b)) =>
            ints(List(a, b)).collect { case List(a, b) if b != 0 => euclidean(a, b)._2 }

          case _ =>
            None

      case _ =>
        None

  def int(expr: Expr): Option[BigInt] =
    apply(expr).collect { case value: BigInt => value }

  def bool(expr: Expr): Option[Boolean] =
    apply(expr).collect { case value: Boolean => value }

  def ints(exprs: List[Expr]): Option[List[BigInt]] =
    exprs.foldRight(Option(List.empty[BigInt])) { (expr, rest) => for v <- int(expr); vs <- rest yield v :: vs }

  def values(exprs: List[Expr]): Option[List[BigInt | Boolean]] =
    exprs.foldRight(Option(List.empty[BigInt | Boolean])) { (expr, rest) => for v <- apply(expr); vs <- rest yield v :: vs }

  def compare(op: String, a: BigInt, b: BigInt): Boolean =
    op match
      case "<"  => a < b
      case "<=" => a <= b
      case ">"  => a > b
      case ">=" => a >= b

  // the quotient and remainder of SMT-LIB, whose remainder is nonnegative, unlike those of BigInt, which truncate
  def euclidean(a: BigInt, b: BigInt): (BigInt, BigInt) =
    val (q, r) = (a / b, a % b)
    if r >= 0 then (q, r)
    else if b > 0 then (q - 1, r + b)
    else (q + 1, r - b)
