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

// extension [A](p: Parser[List[A]])
//   def ::[B >: A](q: Parser[B]): Parser[List[B]] =
//     (q ~ p) { case (a, as) => a :: as }

//   def ++[B >: A](q: Parser[List[B]]): Parser[List[B]] =
//     (p ~ q) { case (as, bs) => as ++ bs }

extension (s: Scanner)
  infix def $[B](f: => B): Parser[B] =
    s ~ R(f)

extension [A1](p: Parser[A1])
  infix def $[B](f: A1 => B): Parser[B] =
    p.map { case (a) => f(a) }

extension [A1, A2](p: Parser[A1 ~ A2])
  infix def $[B](f: (A1, A2) => B): Parser[B] =
    p.map { case a1 ~ a2 => f(a1, a2) }

  def apply[B](f: (A1, A2) => B): Parser[B] =
    p.map { case a1 ~ a2 => f(a1, a2) }

extension [A1, A2, A3](p: Parser[A1 ~ A2 ~ A3])
  infix def $[B](f: (A1, A2, A3) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 => f(a1, a2, a3) }

extension [A1, A2, A3, A4](p: Parser[A1 ~ A2 ~ A3 ~ A4])
  infix def $[B](f: (A1, A2, A3, A4) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 => f(a1, a2, a3, a4) }

extension [A1, A2, A3, A4, A5](p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5])
  infix def $[B](f: (A1, A2, A3, A4, A5) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 => f(a1, a2, a3, a4, a5) }

extension [A1, A2, A3, A4, A5, A6](p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6])
  infix def $[B](f: (A1, A2, A3, A4, A5, A6) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 => f(a1, a2, a3, a4, a5, a6) }

extension [A1, A2, A3, A4, A5, A6, A7](p: Parser[A1 ~ A2 ~ A3 ~ A4 ~ A5 ~ A6 ~ A7])
  infix def $[B](f: (A1, A2, A3, A4, A5, A6, A7) => B): Parser[B] =
    p.map { case a1 ~ a2 ~ a3 ~ a4 ~ a5 ~ a6 ~ a7 => f(a1, a2, a3, a4, a5, a6, a7) }
