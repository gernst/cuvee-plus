package cuvee.sexpr

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

object Id extends (String => Atom)
object Kw extends (String => Atom)
object Str extends (String => Atom)
object Num extends (String => Atom)
object Dec extends (String => Atom)
object Hex extends (String => Atom)
object Bin extends (String => Atom)

object Syntax:
  val lp = Token.Keyword("(")
  val rp = Token.Keyword(")")

  def value(name: String, text: String) =
    Token.Value(name, text)

  def error(msg: String) =
    Error.report(msg)
