package cuvee.test

import utest.Tests
import utest.framework.Tree
import utest.framework.TestCallTree

import cuvee.Error

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

  // runs Cuvee on `args` and returns the messages of all errors that are reported
  def errors(args: String*): List[String] =
    val (_, results) = cuvee.Cuvee.run(args*)
    results.collect { case error: Error => error.msg }
