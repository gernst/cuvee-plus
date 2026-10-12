package cuvee.pipe

import java.io.Reader
import java.io.InputStreamReader
import java.io.FileReader
import java.nio.charset.StandardCharsets
import java.nio.file.Files
import java.nio.file.Path
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
// which the output drops (see Sink.known)
trait Source:
  def newScanner(reader: Reader): Scanner

  // a parser whose state holds the declarations of the prelude, and these declarations,
  // where the configuration may affect parsing, e.g. the data model of C
  def newParser(config: Config): (State, easyparse.Parser[List[Cmd]], List[Cmd])

  // the resources with further definitions that are injected after the prelude, in order,
  // which may depend on the configuration
  def preludes(config: Config): List[String]

  // files on the classpath, such as the preludes, bundled from resources/
  def resource(path: String): Reader =
    val stream = getClass.getResourceAsStream(path)

    Error.report("resource not found", path):
      require(stream != null)

    new InputStreamReader(stream, StandardCharsets.UTF_8)

  // files of the user, such as those of -include
  def file(path: String): Reader =
    Error.report("file not found", path):
      require(Files.isRegularFile(Path.of(path)))

    new FileReader(path, StandardCharsets.UTF_8)

  def apply(reader: Reader): (State, LazyList[Cmd]) =
    apply(Config.default, reader)

  def apply(config: Config, reader: Reader): (State, LazyList[Cmd]) =
    val (init, parser, prelude) = newParser(config)

    val preludes_ =
      for path <- preludes(config); cmd <- parse(path, parser)
      yield cmd

    // the modules of the lemma database (see Config.injected), on which the TEQ
    // transform relies, parsed by the parser of the input if they are in the same language, such that the input can
    // refer to them, otherwise by a fresh parser of their language, one per language for all of its files, such that
    // later files can refer to the declarations of earlier ones, e.g. the modules to the core of the database
    val parsers = scala.collection.mutable.Map[Source, easyparse.Parser[List[Cmd]]]()

    def parserOf(source: Source) =
      if source == this then parser else parsers.getOrElseUpdate(source, source.newParser(config)._2)

    val modules_ =
      for
        (source, path) <- config.injected
        cmd <- source.parse(path, parserOf(source))
      yield cmd

    // the files of the user (-include), after the modules, such that they can refer to them, parsed in the
    // same way; a file in another language starts from the prelude of its source and the modules in that
    // language, not from the state of the input
    val includes_ =
      for
        (source, path) <- config.includes
        cmd <- source.include(path, parserOf(source))
      yield cmd

    val prelude_ = prelude ++ preludes_ ++ modules_ ++ includes_

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

  // the commands of a file of the user
  def include(path: String, parser: easyparse.Parser[List[Cmd]]): List[Cmd] =
    val reader = file(path)
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
