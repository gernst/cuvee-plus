package cuvee.prove

import cuvee.core.*

// the values of closed terms of the functions that are computed from literals, for the counterexample search of
// Prove: an instance of a goal at literal values is evaluated directly, without the rules, the classes and the
// simplex, which may decide anything in a context whose contradiction they do not detect (e.g. the premise
// 4294967296 <= 0 of a case that the instance does not satisfy); integers are BigInt; a term without a value (a
// variable, a division by zero, another function) has none
object Eval:
  // the functions whose values are computed from literals, without quantifiers
  val computed = Set("and", "or", "not", "=>", "=", "distinct", "<", "<=", ">", ">=", "+", "-", "*", "div", "mod", "ite", "true", "false")

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

  // a goal that remains and has no traces, lists, or other functions than those of arithmetic and logic left, e.g.
  // forall N :: !(0 < N && N <= 536870911) of an unsafe task, is refuted by a counterexample among small values and
  // the literals of the goal, plus or minus 1, which its instance evaluates to false at: the goal is false then, which
  // a sink answers incorrect unless the goal is :abstract (see Sink.passive); at most four variables; the instances
  // are evaluated (see apply), not simplified, since the rules decide anything in a context whose contradiction the
  // theories miss, e.g. the premise 4294967296 <= 0 of a case that the instance does not satisfy
  def counterexample(cmd: Cmd): Cmd =
    cmd match
      case Assert(justify, Nil, phi, attrs) if phi != True && phi != False =>
        val (xs, body) =
          phi match
            case All(xs, body) => (xs, body)
            case _             => (Nil, phi)

        val scalar = xs.forall(x => x.typ == Sort.int || x.typ == Sort.bool)
        if xs.length > 4 || !scalar || !evaluable(body) || !body.free.subsetOf(xs.toSet)
        then cmd
        else
          val ints = (literals(body) ++ List(BigInt(0), BigInt(1), BigInt(-1))).flatMap(c => List(c - 1, c, c + 1)).distinct.take(24)
          val choices =
            for x <- xs
            yield
              if x.typ == Sort.bool then List(True, False)
              else ints.map(c => Lit(c, Sort.int))

          val refuted = assignments(choices).take(4096).exists(values => bool(Subst.from(xs, values)(body)) == Some(false))
          if refuted then Assert(justify, Nil, False, attrs) else cmd

      case _ =>
        cmd

  def literals(expr: Expr): List[BigInt] =
    expr match
      case Lit(value: BigInt, _) => List(value)
      case App(_, _, _, args)    => args.flatMap(literals)
      case _                     => Nil

  def assignments(choices: List[List[Expr]]): LazyList[List[Expr]] =
    choices match
      case Nil          => LazyList(Nil)
      case xs :: rest   => for x <- LazyList.from(xs); tail <- assignments(rest) yield x :: tail
