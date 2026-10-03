package cuvee.pipe

import java.io.Reader
import java.io.InputStreamReader
import java.nio.charset.StandardCharsets
import easyparse.Token

import cuvee.Error
import cuvee.core._
import cuvee.smtlib.Parser

// produces the commands together with the initial state of the parser,
// which must be shared by all stages of the pipeline
trait Source extends (Reader => (State, LazyList[Cmd])):
  def newScanner(reader: Reader): Scanner
  def newParser(): (State, easyparse.Parser[List[Cmd]])

  // files on the classpath, such as the preludes, bundled from resources/
  def resource(path: String): Reader =
    val stream = getClass.getResourceAsStream(path)

    Error.report("resource not found", path):
      require(stream != null)

    new InputStreamReader(stream, StandardCharsets.UTF_8)

  def apply(reader: Reader): (State, LazyList[Cmd]) =
    val scanner = newScanner(reader)
    val (init, parser) = newParser()

    // defer parsing such that errors in the first command are reported by the pipeline, too
    (init, LazyList.empty #::: cmds(scanner.input, parser))

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
