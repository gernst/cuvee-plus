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

object Syntax:
  val lp = Token.Keyword("(")
  val rp = Token.Keyword(")")
  val eof = Token.eof

  def value(name: String, text: String) =
    Token.Value(name, text)

  def error(msg: String) =
    Error.report(msg)

