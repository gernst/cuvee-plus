package cuvee.sexpr

import cuvee.sexpr._
import cuvee.core.State

object Grammar:
  import easyparse._
  import Brackets._

  val id = Id(T("id"))
  val kw = Kw(T("kw"))
  val str = Str(T("str"))
  val num = Num(T("num"))
  val dec = Dec(T("dec"))
  val hex = Hex(T("hex"))
  val bin = Bin(T("bin"))

  val atom: Parser[Any] =
    P(id | kw | str | num | dec | hex | bin)

  val sexpr: Parser[Any] =
    P(parens(sexprs) | atom)

  val sexprs = sexpr.*
