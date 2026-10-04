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

  // runs Cuvee on `args` and returns the messages of all errors that are reported
  def errors(args: String*): List[String] =
    val (_, results) = cuvee.Cuvee.run(args*)
    results.collect { case error: Error => error.msg }

  // runs Cuvee on `args` and returns the commands that reach the sink, i.e., after all transforms,
  // together with the messages of all errors that are reported
  def output(args: String*): (List[Cmd], List[String]) =
    val buffer = mutable.ListBuffer[Cmd]()
    val (_, results) = cuvee.Cuvee.run(args.toList, List(Sink.collect(buffer)))
    (buffer.toList, results.collect { case error: Error => error.msg })

  // runs Cuvee on `args` and returns the parsed input commands
  def input(args: String*): List[Cmd] =
    val (cmds, _) = cuvee.Cuvee.run(args*)
    cmds
