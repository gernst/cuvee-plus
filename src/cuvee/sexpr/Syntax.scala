package cuvee.sexpr

import java.util.regex.Pattern

import scala.reflect.ClassTag

import cuvee.Error
import easyparse.Token

sealed trait Atom:
  def text: String

case class Id(text: String) extends Atom
case class Kw(text: String) extends Atom
case class Str(text: String) extends Atom
case class Num(text: String) extends Atom
case class Dec(text: String) extends Atom
case class Hex(text: String) extends Atom
case class Bin(text: String) extends Atom

object Syntax:
  val lp = Token.Keyword("(")
  val rp = Token.Keyword(")")
  val eof = Token.eof

  def value(name: String, text: String) =
    Token.Value(name, text)

  def error(msg: String) =
    Error.report(msg)

object Attrs:
  val empty = Attrs(Nil)

case class Attrs(attrs: List[(String, Option[Any])]):
  infix def ++(that: Attrs) =
    Attrs(this.attrs ++ that.attrs)

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
      case (kw, None)         => List(kw)
      case (kw, Some(sSExpr)) => List(kw, sSExpr)
