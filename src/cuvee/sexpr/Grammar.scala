package cuvee.sexpr

object Grammar:
  import easyparse._
  import Brackets._

  def atom: Parser[Any] =
    P(???)

  val sexprs =
    sexpr.*

  val sexpr: Parser[Any] =
    P(parens(sexprs) | atom)
