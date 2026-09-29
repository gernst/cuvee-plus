package easyparse

import scala.collection.IterableFactory

import util.or

trait Parser[+A]:
  def parse(in: Input, cm: Boolean): (A, Input)

  def parse(in: Input): (A, Input) =
    parse(in, cm = true)

  def parseAll(in: Input): A =
    val (a, in_) = this.parse(in)
    if (in_.nonEmpty) Input.fail("<eof>", in_, true)
    else a

  def asScanner: Scanner =
    Scanner.Discard(this)

  def map[B](f: A => B): Parser[B] =
    Parser.Apply(this, f)

  def flatMap[B](f: A => List[B]): Parser[List[B]] =
    Parser.Apply(this, f)

  def collect[B](f: PartialFunction[A, B])(implicit name: sourcecode.Name): Parser[B] =
    Parser.Collect(name.value, this, f)

  def filter(f: A => Boolean)(implicit name: sourcecode.Name): Parser[A] =
    Parser.Filter(name.value, this, f)

  infix def |[B >: A](that: Parser[B]): Parser[B] =
    Parser.Choice(this, that)

  infix def ~[B](that: Parser[B]): Parser[(A, B)] =
    Parser.SeqParser(this, that, strict = true)

  infix def ~(that: Scanner): Parser[A] =
    Parser.SeqScanner(this, that, strict = true)

  infix def ?~[B](that: Parser[B]): Parser[(A, B)] =
    Parser.SeqParser(this, that, strict = false)

  infix def ?~(that: Scanner): Parser[A] =
    Parser.SeqScanner(this, that, strict = false)

  def ? : Parser[Option[A]] =
    Parser.Repeat(this, 0, 1).map {
      case List()  => None
      case List(a) => Some(a)
      case _       => ???
    }

  def * : Parser[List[A]] =
    Parser.Repeat(this, 0, Int.MaxValue)

  def + : Parser[List[A]] =
    Parser.Repeat(this, 1, Int.MaxValue)

  def ~*(sep: Scanner): Parser[List[A]] =
    Parser.Intersperse(this, sep, false)

  def ~+(sep: Scanner): Parser[List[A]] =
    Parser.Intersperse(this, sep, true)

  def unfold[CC[+_]](factory: IterableFactory[CC])(in: Input): CC[A] =
    val p = this.?
    val b = factory.newBuilder[(A, Input)]

    factory.unfold(in): in0 =>
      val (a, in1) = p.parse(in0)
      a map { (_, in1) }

object Parser:
  case class Recursive[A](name: String, p: () => Parser[A]) extends Parser[A]:
    def parse(in0: Input, cm: Boolean) =
      try p().parse(in0, cm)
      catch
        case Fail(in1, trace) =>
          throw Fail(in1, name :: trace)

  case class Accept[A](a: A) extends Parser[A]:
    def parse(in: Input, cm: Boolean) =
      (a, in)

  case class Match(name: String) extends Parser[String]:
    def parse(in: Input, cm: Boolean) =
      Input.shift(name, in, cm):
        case (Token.Value(`name`, value), in_) =>
          (value, in_)

  case class Apply[A, +B](p: Parser[A], f: A => B) extends Parser[B]:
    def parse(in0: Input, cm: Boolean) =
      val (a, in1) = p.parse(in0, cm)
      (f(a), in1)

  case class Collect[A, +B](name: String, p: Parser[A], f: PartialFunction[A, B]) extends Parser[B]:
    def parse(in0: Input, cm: Boolean) =
      val (a, in1) = p.parse(in0, cm)
      if f.isDefinedAt(a)
      then (f(a), in1)
      else Input.fail(name, in0, cm)

  case class Filter[A](name: String, p: Parser[A], f: A => Boolean) extends Parser[A]:
    def parse(in0: Input, cm: Boolean) =
      val (a, in1) = p.parse(in0, cm)
      if f(a) then (a, in1)
      else Input.fail(name, in0, cm)

  case class Choice[+A](p: Parser[A], q: Parser[A]) extends Parser[A]:
    def parse(in: Input, cm: Boolean) =
      p.parse(in, cm = false) or q.parse(in, cm)

  case class SeqParser[+A, +B](p: Parser[A], q: Parser[B], strict: Boolean) extends Parser[(A, B)]:
    def parse(in0: Input, cm: Boolean) =
      val (a, in1) = p.parse(in0, cm)
      val (b, in2) = q.parse(in1, cm || strict)
      ((a, b), in2)

  case class SeqScanner[+A](p: Parser[A], q: Scanner, strict: Boolean) extends Parser[A]:
    def parse(in0: Input, cm: Boolean) =
      val (a, in1) = p.parse(in0, cm)
      val in2 = q.scan(in1, cm || strict)
      (a, in2)

  case class Intersperse[+A](p: Parser[A], q: Scanner, min: Boolean) extends Parser[List[A]]:
    def parse(in0: Input, cm: Boolean): (List[A], Input) =
      if min
      then
        val (a, in1) = p.parse(in0, cm)
        val (as, in2) = more(in1)
        (a :: as, in2)
      else
        {
          val (a, in1) = p.parse(in0, false)
          val (as, in2) = more(in1)
          (a :: as, in2)
        } or {
          (Nil, in0)
        }

    def more(in0: Input): (List[A], Input) = {
      // the separator to parse further is always optional
      val in1 = q.scan(in0, false)
      // but if present, we need another element
      val (a, in2) = p.parse(in1, true)
      val (as, in3) = more(in2)
      (a :: as, in3)
    } or {
      (Nil, in0)
    }

  case class Repeat[+A](p: Parser[A], min: Int, max: Int) extends Parser[List[A]]:
    require(0 <= min && min <= max)

    def parse(in: Input, cm: Boolean): (List[A], Input) =
      parse(0, in, cm)

    def parse(done: Int, in0: Input, cm: Boolean): (List[A], Input) =
      if done < min
      then
        val (a, in1) = p.parse(in0, cm)
        val (as, in2) = this.parse(done + 1, in1, cm)
        (a :: as, in2)
      else if done < max && in0.nonEmpty
      then
        {
          val (a, in1) = p.parse(in0, false)
          val (as, in2) = this.parse(done + 1, in1, cm)
          (a :: as, in2)
        } or {
          (Nil, in0)
        }
      else (Nil, in0)
