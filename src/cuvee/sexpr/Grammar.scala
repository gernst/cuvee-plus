package cuvee.sexpr

import cuvee.sexpr._
import cuvee.core.State

object Grammar extends cuvee.pipe.Grammar:
  val init = State.default
  val cmd = sexpr

  import easyparse._
  import Brackets._

  val id = T("id") $ { Id(_) }
  val kw = T("kd") $ { Kw(_) }
  val str = T("str") $ { Str(_) }
  val num = T("num") $ { Num(_) }
  val dec = T("dec") $ { Dec(_) }
  val hex = T("hex") $ { Hex(_) }
  val bin = T("bin") $ { Bin(_) }

  val atom: Parser[Any] =
    P(id | kw | str | num | dec | hex | bin)

  val sexpr: Parser[Any] =
    P(parens(sexprs) | atom)

  val sexprs = sexpr.*