package cuvee.pipe

import java.io.IOException
import cuvee.core.State

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