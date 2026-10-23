package cuvee.test

import java.io.ByteArrayOutputStream
import java.io.PrintStream
import java.nio.charset.StandardCharsets.UTF_8
import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters._

import cuvee.Config
import cuvee.Cuvee
import cuvee.core._
import cuvee.pipe._

// an example as a test of its command line, stated in its first line as a comment of its language,
// which can be pasted into a shell in the root of the repository, e.g.
//   ; ./Cuvee.sh -prove examples/smtlib/simplify/arith.smt2
// whose last argument is the example itself; the expected output and reports are the lines that stdout and stderr show,
// in name.out and name.err next to the example, where a missing file stands for no lines;
// the reports are compared as text, and so is the output of examples in a directory named printing,
// otherwise the output is compared as commands, both parsed in the language of the output, which ignores the layout;
// nothing is written, the lines of stdout and stderr are captured in memory (see Config.stdout and Config.stderr)
object Expected:
  // ./Cuvee.sh -test <file> in the root of the repository: prints the command line and the differences,
  // returns the exit code, 0 if the example meets its expected output
  def main(file: String): Int =
    val root = Path.of("").toAbsolutePath
    check(root, root.resolve(file).normalize) match
      case Nil =>
        println("ok " + file)
        0

      case diffs =>
        for diff <- diffs
        do println(diff)
        1

  // the command line of an example, without ./Cuvee.sh, if its first line states one
  def command(root: Path, file: Path): Option[List[String]] =
    val lines = Files.readAllLines(file).asScala
    val words = lines.headOption.getOrElse("").dropWhile(c => c == '/' || c == ';' || c == '#').trim.split(" +").toList
    val path = root.relativize(file).toString

    words match
      case "./Cuvee.sh" :: args if args.lastOption.contains(path) => Some(args)
      case _                                                     => None

  // the lines of an expected output, none if the file does not exist
  def expected(file: Path, ext: String): List[String] =
    val name = file.getFileName.toString
    val path = file.resolveSibling(name.take(name.lastIndexOf('.')) + "." + ext)
    if Files.exists(path) then Files.readAllLines(path).asScala.toList else Nil

  // runs the command line `args` on `file` and returns the lines that stdout and stderr would show,
  // i.e., the output and the reports, and the configuration; the width of the lines is the default one of a new run,
  // since the printers keep it globally (see Config.linewidth)
  def run(args: List[String], file: Path): (List[String], List[String], Config) =
    val out = new ByteArrayOutputStream
    val err = new ByteArrayOutputStream
    val default = Config.default.copy(stdout = new PrintStream(out, true, UTF_8), stderr = new PrintStream(err, true, UTF_8))
    val config = Config.parse(default, List("-linewidth", "80") ++ args.init :+ file.toString)
    Cuvee.pipe(config, Nil)
    (out.toString(UTF_8).linesIterator.toList, err.toString(UTF_8).linesIterator.toList, config)

  // the commands of the output `lines`, parsed in the language of the output, without its prelude,
  // whose fresh names are numbered from the start as in Cuvee.pipe
  def parse(config: Config, lines: List[String]): List[Cmd] =
    val lang = config.output
    val config_ = config.copy(input = lang)
    Var.reset()
    Param.reset()
    val (_, cmds) = lang.source(config_, new java.io.StringReader(lines.mkString("\n")))
    val (_, prelude) = lang.source(config_, new java.io.StringReader(""))
    cmds.toList.filterNot(prelude.toList.contains)

  // whether the output of `file` is compared as text
  def text(file: Path): Boolean =
    file.iterator.asScala.exists(_.toString == "printing")

  // the differences of the example `file` below `root` to its expected output, none if it meets it
  def check(root: Path, file: Path): List[String] =
    command(root, file) match
      case None =>
        val path = root.relativize(file)
        List(s"$path: the first line is not a command line ./Cuvee.sh ... $path")

      case Some(args) =>
        val (out, err, config) = run(args, file)
        val out_ = expected(file, "out")
        val err_ = expected(file, "err")

        val diffs =
          diff("stderr", err_, err) ++
            (if out == out_ then Nil
             else if text(file) then diff("stdout", out_, out)
             else
               val (cmds, cmds_) = (parse(config, out_), parse(config, out))
               if cmds == cmds_ then Nil else diff("stdout (as commands)", out_, out))

        if diffs.isEmpty then Nil
        else ("./Cuvee.sh" :: args).mkString(" ") :: diffs

  // the expected and actual lines from the first one that differs
  def diff(what: String, expected: List[String], actual: List[String]): List[String] =
    if expected == actual then Nil
    else
      val same = expected.zip(actual).takeWhile(_ == _).length
      List(
        s"$what differs from line ${same + 1}, expected:",
        expected.drop(same).mkString("\n"),
        "actual:",
        actual.drop(same).mkString("\n")
      )
