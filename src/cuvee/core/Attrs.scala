package cuvee.core

import scala.reflect.ClassTag

import cuvee.sexpr.Kw

object Attrs:
  def empty = Attrs(Nil)

// the attributes of declarations, loops, and differential equations as keywords with optional values,
// as SMT-LIB annotations; the frontends store resolved values, e.g. expressions for contracts
case class Attrs(attrs: List[(String, Option[Any])]):
  def isEmpty =
    attrs.isEmpty

  def contains(kw: String) =
    attrs.exists:
      case (kw_, _) => kw == kw_

  def get(kw: String) =
    attrs.collect:
      case (`kw`, arg) => arg

  def values[T: ClassTag](kw: String) =
    attrs.collect:
      case (`kw`, Some(arg: T)) => arg

  // apply `f` to the expressions among the values
  def map(f: Expr => Expr): Attrs =
    val attrs_ =
      for (kw, arg) <- attrs
      yield arg match
        case Some(expr: Expr) => (kw, Some(f(expr)))
        case _                => (kw, arg)

    Attrs(attrs_)

  // the free variables of the expressions among the values, e.g. of loop invariants
  def free: Set[Var] =
    attrs.flatMap(_._2).collect { case expr: Expr => expr.free }.flatten.toSet

  def flatten =
    attrs flatMap:
      case (kw, None)      => List(Kw(kw))
      case (kw, Some(arg)) => List(Kw(kw), arg)

  // the contracts of procedures, conjunctions of the clauses
  def requires: Expr =
    And(values[Expr]("requires"))

  def ensures: Expr =
    And(values[Expr]("ensures"))

  // the global variables modified by procedures and loops
  def modifies: List[Var] =
    values[List[Var]]("modifies").flatten.distinct

  // the components of a lexicographic termination measure, of procedures and loops
  def decreases: List[Expr] =
    values[Expr]("decreases")

  // the invariants of loops, and the differential invariants of differential equations, in order
  def invariants: List[Expr] =
    values[Expr]("invariant")

  def invariant: Expr =
    And(invariants)

  // the assumption-commitment contracts of procedures over the history, for parallel composition
  def assumes: Expr =
    And(values[Expr]("assumes"))

  def commits: Expr =
    And(values[Expr]("commits"))
