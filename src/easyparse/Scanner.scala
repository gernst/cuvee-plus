package easyparse

import util.or

trait Scanner:
  def scan(in: Input, cm: Boolean): Input

  def ~[B](that: Parser[B]): Parser[B] =
    Scanner.SeqParser(this, that, strict = true)

  def ~(that: Scanner): Scanner =
    Scanner.SeqScanner(this, that, strict = true)

object Scanner:
  case object Accept extends Scanner:
    def scan(in: Input, cm: Boolean) =
      in

  case class Match(name: String) extends Scanner:
    def scan(in: Input, cm: Boolean) =
      Input.shift(name, in, cm):
        case (Token.Keyword(`name`), in_) =>
          in_

  case class Choice(p: Scanner, q: Scanner) extends Scanner:
    def scan(in: Input, cm: Boolean) =
      p.scan(in, cm = false) or q.scan(in, cm)

  case class Discard[A](p: Parser[A]) extends Scanner:
    def scan(in: Input, cm: Boolean) =
      val (_, in_) = p.parse(in, cm)
      in_

  case class SeqParser[+B](p: Scanner, q: Parser[B], strict: Boolean) extends Parser[B]:
    def parse(in0: Input, cm: Boolean) =
      val in1 = p.scan(in0, cm)
      val (b, in2) = q.parse(in1, cm || strict)
      (b, in2)

  case class SeqScanner(p: Scanner, q: Scanner, strict: Boolean) extends Scanner:
    def scan(in0: Input, cm: Boolean) =
      val in1 = p.scan(in0, cm)
      val in2 = q.scan(in1, cm || strict)
      in2
