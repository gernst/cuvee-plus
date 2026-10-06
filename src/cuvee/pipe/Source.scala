package cuvee.pipe

import java.io.Reader
import java.io.InputStreamReader
import java.nio.charset.StandardCharsets
import easyparse.Token

import cuvee.Config
import cuvee.Error
import cuvee.core._
import cuvee.smtlib.Parser

// produces the commands together with the initial state of the parser,
// which must be shared by all stages of the pipeline:
// the initial state holds the declarations of the prelude of the frontend (prelude.*),
// the commands begin with these and further definitions that depend on the configuration (e.g. hybrid.dfy),
// where the commands of the input that coincide with them are dropped, e.g. when printed output is parsed again;
// the declarations of the prelude name the languages that they are part of,
// which the output drops (see cuvee.transform.Language)
trait Source:
  def newScanner(reader: Reader): Scanner

  // a parser whose state holds the declarations of the prelude, and these declarations,
  // where the configuration may affect parsing, e.g. the data model of C
  def newParser(config: Config): (State, easyparse.Parser[List[Cmd]], List[Cmd])

  // the resources with further definitions that are injected after the prelude, in order,
  // which may depend on the configuration
  def preludes(config: Config): List[String] = Nil

  // files on the classpath, such as the preludes, bundled from resources/
  def resource(path: String): Reader =
    val stream = getClass.getResourceAsStream(path)

    Error.report("resource not found", path):
      require(stream != null)

    new InputStreamReader(stream, StandardCharsets.UTF_8)

  def apply(reader: Reader): (State, LazyList[Cmd]) =
    apply(Config.default, reader)

  def apply(config: Config, reader: Reader): (State, LazyList[Cmd]) =
    val (init, parser, prelude) = newParser(config)

    val injected =
      for path <- preludes(config); cmd <- parse(path, parser)
      yield cmd

    val prelude_ = prelude ++ injected

    // defer reading and parsing such that errors in the first command are reported by the pipeline, too
    (init, LazyList.empty #::: prelude_.to(LazyList) #::: input(config, reader, parser).filterNot(prelude_.contains))

  // the commands of the input, evaluated on demand
  def input(config: Config, reader: Reader, parser: easyparse.Parser[List[Cmd]]): LazyList[Cmd] =
    cmds(newScanner(reader).input, parser)

  // the commands of a resource
  def parse(path: String, parser: easyparse.Parser[List[Cmd]]): List[Cmd] =
    val reader = resource(path)
    try cmds(newScanner(reader).input, parser).toList
    finally reader.close()

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
