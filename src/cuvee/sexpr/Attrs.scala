package cuvee.sexpr

import scala.reflect.ClassTag

object Attrs:
  val empty = Attrs(Nil)

case class Attrs(attrs: List[(String, Option[Any])]):
  infix def ++(that: Attrs) =
    Attrs(this.attrs ++ that.attrs)

  infix def +(kw: String) =
    Attrs(attrs ++ List(kw -> None))

  infix def +(kw: String, arg: Any) =
    Attrs(attrs ++ List(kw -> Some(arg)))

  infix def ++(kw: String, args: List[Any]) =
    Attrs(attrs ++ args.map(kw -> Some(_)))

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

  def flatten =
    attrs flatMap:
      case (kw, None)      => List(Kw(kw))
      case (kw, Some(arg)) => List(Kw(kw), arg)
