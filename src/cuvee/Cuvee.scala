package cuvee

import java.io.IOException

import scala.util.control.Breaks
import java.io.InputStreamReader

import cuvee.core._

case class Fatal(msg: String) extends Throwable:
  override def toString =
    "Fatal(" + msg + ")"

object Error:
  def report(msg: String) =
    throw cuvee.core.Error(msg)

  def reportIf(msg: String, phi: Boolean) =
    if phi then report(msg)

  def abort(msg: String) =
    throw Fatal(msg)

  def abortIf(msg: String, phi: Boolean) =
    if phi then abort(msg)

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

case class Name(name: String, index: Option[Int])

object Name:
  given Conversion[String, Name] =
    (name: String) => Name(name, None)

@main
def run() =
  import cuvee.pipe._

  val scanner = sexpr.Scanner(new InputStreamReader(System.in))
  val grammar = sexpr.Grammar
  val source = Source.read(State.default, scanner, grammar)

  val printer = Printer.default
  val sink = Sink.stdout(printer)

  val report = Report.stderr(printer)

  Pipe.run(source, sink, report, true)
