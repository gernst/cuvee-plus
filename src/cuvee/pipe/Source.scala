package cuvee.pipe

import cuvee.Error
import cuvee.core._
import cuvee.smtlib.Parser
import java.io.Reader

trait Source extends (Reader => Iterable[Cmd]):
  def newScanner(reader: Reader): Scanner
  def newParser(): easyparse.Parser[List[Cmd]]

  def apply(reader: Reader): LazyList[Cmd] =
    val scanner = newScanner(reader)
    cmds(scanner.input, newParser())

  def cmds(in: easyparse.Input, parser: easyparse.Parser[List[Cmd]]): LazyList[Cmd] =
    if in.isEmpty || in.head == null
    then LazyList.empty
    else
      try
        val (chunk, in_) = parser.parse(in, true)
        LazyList(chunk*) #::: cmds(in_, parser)
      catch
        case easyparse.Fail(in, from) =>
          in.take(10).toList // force lazy prefix as side-effect
          Error.raise("parse error", from, in)
