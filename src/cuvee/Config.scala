package cuvee

import java.io.IOException

import scala.util.control.Breaks

import cuvee.core._

case class Config(
    printer: Printer
)

trait Scanner:
  import easyparse._

  @throws[IOException]
  def next: Token

  def input: Input =
    next match
      case Token.eof =>
        Input.empty

      case token =>
        Input.cons(token, input)

trait Grammar:
  def init: State
  def cmd: easyparse.Parser[Any]

trait Printer:
  def lines(res: Result): List[String]
  def lines(cmd: Cmd): List[String]
  def lines(typ: Type): List[String]
  def lines(expr: Expr): List[String]

object Printer:
  object default extends Printer:
    def lines(res: Result) = List(res.toString)
    def lines(cmd: Cmd) = List(cmd.toString)
    def lines(typ: Type) = List(typ.toString)
    def lines(expr: Expr) = List(expr.toString)
