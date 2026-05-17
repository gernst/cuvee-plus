package cuvee.sexpr

import scala.reflect.ClassTag
import java.util.regex.Pattern

sealed trait Atom:
  def text: String

case class Id(text: String) extends Atom
case class Kw(text: String) extends Atom

object Id:
  val simple =
    Pattern.compile("[:]?[a-zA-Z_~!@$%^&*+=<>.?/\\-][0-9a-zA-Z_~!@$%^&*+=<>.?/\\-]*")

  def mangle(str: String) =
    if simple.matcher(str).matches()
    then str
    else "|" + str + "|"

object Attrs:
  val empty = Attrs(Nil)

case class Attrs(attrs: List[(String, Option[Any])]):
  infix def ++(that: Attrs) =
    Attrs(this.attrs ++ that.attrs)

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
      case (kw, None)         => List(kw)
      case (kw, Some(sSExpr)) => List(kw, sSExpr)
