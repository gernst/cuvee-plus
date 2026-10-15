package easyparse

import util.backtrack

type Input = LazyList[Token]

type ~[+A, +B] = Tuple2[A, B]
val ~ = Tuple2

def R[A](a: A): Parser[A] =
  Parser.Accept(a)

implicit def S(name: String): Scanner =
  Scanner.Match(name)

def T(name: String): Parser[String] =
  Parser.Match(name)

// the line and column of the keyword `name`, which the scanner has located
def L(name: String): Parser[(Int, Int)] =
  Parser.Locate(name)

def J(name: String): Parser[String] =
  S(name).map(name)

def P[A](p: => Parser[A])(implicit name: sourcecode.Name): Parser[A] =
  Parser.Recursive(name.value, () => p)

object Brackets:
  def parens[A](p: Parser[A]) =
    "(" ~ p ~ ")"

  def brackets[A](p: Parser[A]) =
    "[" ~ p ~ "]"

  def braces[A](p: Parser[A]) =
    "{" ~ p ~ "}"

object Input:
  val empty: Input =
    LazyList.empty[Token]

  def cons(tok: Token, in: => Input): Input =
    tok #:: in

  def shift[A](where: String, in: Input, cm: Boolean)(pf: PartialFunction[(Token, Input), (A, Input)]) =
    in match
      case tok #:: in_ if pf.isDefinedAt((tok, in_)) =>
        pf((tok, in_))

      case _ =>
        Input.fail(where, in, cm)

  def shift[A](where: String, in: Input, cm: Boolean)(pf: PartialFunction[(Token, Input), Input]) =
    in match
      case tok #:: in_ if pf.isDefinedAt((tok, in_)) =>
        pf((tok, in_))

      case _ =>
        Input.fail(where, in, cm)

  def fail(where: String, in: Input, cm: Boolean) =
    if cm
    then throw Fail(in, List(where))
    else backtrack

sealed trait Token:
  def text: String

object Token:
  val eof = Keyword("<eof>")

  case class Keyword(name: String) extends Token:
    def text = name
    
  case class Value(name: String, text: String) extends Token

  // a keyword (whose text is its name) or a value with the position of its first character, 1-based, for the
  // constructs whose location a frontend reports, e.g. the loops of C and the calls of reach_error for witnesses;
  // it matches as the keyword or the value (see Scanner.Match and Parser.Match)
  case class Located(name: String, text: String, line: Int, column: Int) extends Token

case class Fail(in: Input, from: List[String]) extends Exception
