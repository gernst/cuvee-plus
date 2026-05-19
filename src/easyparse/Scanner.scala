package easyparse

trait Scanner:
  def scan(in: Text, cm: Boolean): Text

  def ~[B](that: Parser[B]): Parser[B] =
    Scanner.SeqParser(this, that, strict = true)

  def ~(that: Scanner): Scanner =
    Scanner.SeqScanner(this, that, strict = true)

object Scanner:
  case object Accept extends Scanner:
    def scan(in: Text, cm: Boolean) =
      in

  case class Match(name: String) extends Scanner:
    def scan(in: Text, cm: Boolean) =
      in match
        case Token.Keyword(`name`) :: in_ =>
          in_
        case _ =>
          Text.fail(in, cm, name)

  case class Dispatch[A](name: String, table: Map[String, Parser[A]]) extends Parser[A]:
    def parse(in: Text, cm: Boolean) =
      in match
        case Token.Keyword(key) :: in_ if table.contains(key) =>
          table(key).parse(in_, cm)
        case _ =>
          Text.fail(in, cm, name)

  case class Choice(p: Scanner, q: Scanner) extends Scanner:
    def scan(in: Text, cm: Boolean) =
      p.scan(in, cm = false) or q.scan(in, cm)

  case class Discard[A](p: Parser[A]) extends Scanner:
    def scan(in: Text, cm: Boolean) =
      val (_, in_) = p.parse(in, cm)
      in_

  case class SeqParser[+B](p: Scanner, q: Parser[B], strict: Boolean) extends Parser[B]:
    def parse(in0: Text, cm: Boolean) =
      val in1 = p.scan(in0, cm)
      val (b, in2) = q.parse(in1, cm || strict)
      (b, in2)

  case class SeqScanner(p: Scanner, q: Scanner, strict: Boolean) extends Scanner:
    def scan(in0: Text, cm: Boolean) =
      val in1 = p.scan(in0, cm)
      val in2 = q.scan(in1, cm || strict)
      in2
