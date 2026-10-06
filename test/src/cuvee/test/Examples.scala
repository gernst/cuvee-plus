package cuvee.test

import utest.Tests
import utest.framework.Tree
import utest.framework.TestCallTree

import scala.collection.mutable

import cuvee.Error
import cuvee.core.Cmd
import cuvee.pipe.Sink

object Examples:
  val root = os.Path(sys.env("MILL_WORKSPACE_ROOT")) / "examples"

  // example files with extension `ext` below `dir`, relative to the examples directory
  def find(dir: os.SubPath, ext: String): List[os.Path] =
    os.walk(root / dir).filter(_.ext == ext).sorted.toList

  // utest builds its test tree at compile time with the Tests macro,
  // therefore the tests for example files found at runtime are assembled by hand,
  // with one test per file, named after the file
  def tests(files: List[os.Path])(body: os.Path => Unit): Tests =
    val names = files.map(file => Tree(file.relativeTo(root).toString))
    val calls = files.map(file => new TestCallTree(Left(body(file))))
    Tests(Tree("", names*), new TestCallTree(Right(calls.toIndexedSeq)))

  // the answer to the last check-sat among the results, e.g. before the model added by -chc
  def status(results: List[cuvee.core.Result]): cuvee.core.Status =
    results.collect { case status: cuvee.core.Status => status }.last

  // the command line options that an example needs, stated in its first line as "// options: -hybrid"
  def options(file: os.Path): List[String] =
    os.read.lines(file).headOption match
      case Some(line) if line.startsWith("// options:") => line.stripPrefix("// options:").trim.split(" +").toList
      case _                                            => Nil

  // runs Cuvee on `args` and returns the messages of all errors that are reported
  def errors(args: String*): List[String] =
    val (_, results) = cuvee.Cuvee.run(args*)
    results.collect { case error: Error => error.msg }

  // runs Cuvee on `args` and returns the commands that reach the sink, i.e., after all transforms,
  // except for the prelude of the frontend, together with the messages of all errors that are reported
  def output(args: String*): (List[Cmd], List[String]) =
    val buffer = mutable.ListBuffer[Cmd]()
    val (_, results) = cuvee.Cuvee.run(args.toList, List(Sink.collect(buffer)))
    (buffer.toList.filterNot(prelude(args*).contains), results.collect { case error: Error => error.msg })

  // the commands of the prelude of the frontend of the input file in `args`
  def prelude(args: String*): List[Cmd] =
    val config = cuvee.Config.parse(cuvee.Config.default, args.toList)
    val (_, cmds) = config.source(config, new java.io.StringReader(""))
    cmds.toList

  // the errors reported for `text` as input in the language of `ext`, parsed and checked only
  def check(ext: String, text: String, options: String*): List[String] =
    val file = os.temp(text, suffix = "." + ext)
    errors(List("-print", "null") ++ options :+ file.toString*)

  // runs Cuvee on `args` and returns the parsed input commands, without the prelude of the frontend
  def input(args: String*): List[Cmd] =
    val (cmds, _) = cuvee.Cuvee.run(args*)
    cmds.filterNot(prelude(args*).contains)
