package cuvee.pipe

import java.io.Reader
import easyparse.Token

import cuvee.Error
import cuvee.core._
import cuvee.smtlib.Parser

trait Source extends (Reader => Iterable[Cmd]):
  def newScanner(reader: Reader): Scanner
  def newParser(): easyparse.Parser[List[Cmd]]

  def apply(reader: Reader): LazyList[Cmd] =
    val scanner = newScanner(reader)
    cmds(scanner.input, newParser())

  def cmds(in: easyparse.Input, parser: easyparse.Parser[List[Cmd]]): LazyList[Cmd] =
    if in.isEmpty || in.head == Token.eof
    then LazyList.empty
    else
      try
        val (chunk, in_) = parser.parse(in, true)
        LazyList(chunk*) #::: cmds(in_, parser)
      catch
        case easyparse.Fail(in, from) =>
          val where = in.take(10).map(_.text).mkString("", " ", " ... ")
          Error.raise("parse error", from, where)
