package cuvee.core

import scala.reflect.ClassTag

import util.Name

import cuvee.sexpr.Kw

object Attrs:
  def empty = Attrs(Nil)

  def from(kw: String) =
    Attrs(List(kw -> None))

// the attributes of declarations, loops, and differential equations as keywords with optional values,
// as SMT-LIB annotations; the frontends store resolved values, e.g. expressions for contracts
case class Attrs(attrs: List[(String, Option[Any])]):
  def isEmpty =
    attrs.isEmpty

  // these attributes followed by those of `that`
  def ++(that: Attrs): Attrs =
    Attrs(attrs ++ that.attrs)

  def contains(kw: String) =
    attrs.exists:
      case (kw_, _) => kw == kw_

  // the attributes with one of the keywords `kws`, e.g. those that solvers understand
  def retain(kws: String*): Attrs =
    Attrs(attrs.filter((kw, _) => kws.contains(kw)))

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

  def args =
    attrs.collect { case (_, Some(expr: Expr)) => expr }

  def free =
    args.free

  def funs =
    args.funs

  def flatten =
    attrs flatMap:
      case (kw, None)      => List(Kw(kw))
      case (kw, Some(arg)) => List(Kw(kw), arg)


  def modifies =
    values[List[Var]]("modifies").flatten.distinct

  def decreases =
    values[Expr]("decreases")

  def invariants =
    values[Expr]("invariant")

  def checks =
    values[Expr]("check-true")

  def tags =
    values[Name]("tag")

  def invariant: Expr =
    And(invariants)

  def requires =
    And(values[Expr]("requires"))

  def ensures =
    And(values[Expr]("ensures"))

  def assumes: Expr =
    And(values[Expr]("assumes"))

  def commits: Expr =
    And(values[Expr]("commits"))
