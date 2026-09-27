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

enum Token:
  case Keyword(name: String)
  case Value(name: String, text: String)

object Token:
  val eof = Keyword("eof")

case class Fail(in: Input, from: List[String]) extends Exception
