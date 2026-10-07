package cuvee.pipe

import java.io.IOException

trait Scanner:
  import easyparse._

  @throws[IOException]
  def next: Token

  // tokens are read only when they are needed, not already when the input is created,
  // so that interactive input such as solver responses does not block
  def input: Input =
    LazyList.continually(next).takeWhile(_ != Token.eof)