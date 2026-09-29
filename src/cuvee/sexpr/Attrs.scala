package cuvee.sexpr

import scala.reflect.ClassTag

import cuvee.Error
import cuvee.core.Expr

object Attrs:
  def empty = Attrs(Nil)

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

  def flatten =
    attrs flatMap:
      case (kw, None)      => List(Kw(kw))
      case (kw, Some(arg)) => List(Kw(kw), arg)
