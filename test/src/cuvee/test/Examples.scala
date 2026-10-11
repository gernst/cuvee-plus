package cuvee.test

import utest.Tests
import utest.ArrowAssert
import utest.framework.Tree
import utest.framework.TestCallTree

import scala.collection.mutable

import cuvee.Error
import cuvee.core.Cmd
import cuvee.pipe.Sink
import cuvee.Cuvee

object Examples:
  val workspace = os.Path(sys.env("MILL_WORKSPACE_ROOT"))
  val root = workspace / "examples"

  // the examples whose output contains implementations of overloaded operators that the solvers do not know yet,
  // e.g. seq.member for x in s (see Fun.seq, TODO.md), which are not passed to them
  val unsupported = Set("dafny/vcgen/seq.dfy")

  def supported(file: os.Path) =
    !unsupported.contains(file.relativeTo(root).toString)

  // directories of examples that are no tests, e.g. experiments that are worked on (none at the moment)
  val excluded: List[os.SubPath] = Nil

  // examples whose runs do not terminate, which are no tests: the two algorithms whose lemmas make the simplifier
  // cycle (see examples/dafny/algorithms/NOTES.md, finding 19)
  val nonterminating = Set("dafny/algorithms/row_sums.dfy", "dafny/algorithms/transpose.dfy")

  def terminating(file: os.Path) =
    !nonterminating.contains(file.relativeTo(root).toString)

  // example files with extension `ext` below `dir`, relative to the examples directory, except the excluded ones and
  // those that do not terminate
  def find(dir: os.SubPath, ext: String): List[os.Path] =
    os.walk(root / dir).filter(_.ext == ext).filter(terminating).filterNot(file => excluded.exists(sub => file.startsWith(root / sub))).sorted.toList

  // utest builds its test tree at compile time with the Tests macro,
  // therefore the tests for example files found at runtime are assembled by hand,
  // with one test per file, named after the file
  def tests(files: List[os.Path])(body: os.Path => Unit): Tests =
    val names = files.map(file => Tree(file.relativeTo(root).toString))
    val calls = files.map(file => new TestCallTree(Left(body(file))))
    Tests(Tree("", names*), new TestCallTree(Right(calls.toIndexedSeq)))

  // a source applied directly, outside of Cuvee.run, whose fresh names are numbered from the start as in Cuvee.pipe,
  // such that they do not depend on the order of the tests
  def source(source: cuvee.pipe.Source, reader: java.io.Reader, config: cuvee.Config = cuvee.Config.default) =
    cuvee.core.Var.reset()
    cuvee.core.Param.reset()
    source(config, reader)

  // the answer to the last check-sat among the results, e.g. before the model added by -chc
  def status(results: List[cuvee.core.Result]): cuvee.core.Status =
    results.collect { case status: cuvee.core.Status => status }.last

  // the options of the languages that an example needs, among those of the command line in its first line,
  // i.e., -hybrid, and the declarations of teq.dfy without its transform for -teq (-known teq), e.g. for inputs that
  // use its types Nat and List
  // and the modules of the lemma database that it includes (-include teq:<concept>), whose declarations its output
  // may refer to
  def options(file: os.Path): List[String] =
    val args = cuvee.test.Expected.command(workspace.toNIO, file.toNIO).getOrElse(Nil)
    val modules = args.zip(args.drop(1)).collect { case ("-include", module) if module.startsWith("teq:") => List("-include", module) }
    args.flatMap {
      case "-hybrid" => List("-hybrid")
      case "-teq"    => List("-known", "teq")
      case _         => Nil
    } ++ modules.flatten

  // whether the goals of an example hold, as stated in its second line, after its command line:
  // "// expected: valid" or "// expected: invalid"
  def holds(file: os.Path): Boolean =
    os.read.lines(file)(1) match
      case "// expected: valid"   => true
      case "// expected: invalid" => false

  // the examples below `dir` with extension `ext` that are accepted, i.e., whose expected reports contain no errors
  // other than goals that do not hold, except for the cases of the frontends and printers in the modules parsing
  // and printing, whose output is checked by its expected output, and the scripts of the module solver, which need one
  def valid(dir: os.SubPath, ext: String): List[os.Path] =
    def cases(file: os.Path) = file.segments.exists(Set("parsing", "printing", "solver"))
    find(dir, ext).filter(file => !cases(file) && reported(file).forall(_ == "goal does not hold"))

  // printing is stable: the output of `args` on `file`, parsed in the language of the output and printed again,
  // is the same text
  // after `rounds` further rounds of parsing and printing, e.g. C, whose first output may still change
  def roundtrip(file: os.Path, args: List[String], rounds: Int = 0): Unit =
    show(args :+ file.toString)
    val (out, err, config) = cuvee.test.Expected.run(args :+ file.toString, file.toNIO)
    errors(err) ==> Nil
    def again(lines: List[String]) =
      config.output.printer.lines(cuvee.test.Expected.parse(config, lines).filterNot(Sink.known(config.output.features, _)))
    val first = (1 to rounds).foldLeft(out)((lines, _) => again(lines))
    again(first).mkString("\n") ==> first.mkString("\n")

  // the command line `args` as it can be pasted into a shell in the root of the repository
  def show(args: Seq[String]): Unit =
    println(("./Cuvee.sh" +: args.map(_.replace(workspace.toString + "/", ""))).mkString(" "))

  // the messages of the errors among the expected reports of an example, e.g. "goal does not hold"
  def reported(file: os.Path): List[String] =
    errors(cuvee.test.Expected.expected(file.toNIO, "err"))

  // the messages of the errors among the lines of reports
  def errors(lines: List[String]): List[String] =
    "error\\s+\"([^\"]*)\"".r.findAllMatchIn(lines.mkString("\n")).map(_.group(1)).toList

  // runs Cuvee on `args` and returns the messages of all errors that are reported
  def errors(args: String*): List[String] =
    show(args)
    val (_, results) = Cuvee.run(args*)
    results.collect { case error: Error => error.msg }

  // runs Cuvee on `args` and returns the commands that reach the sink, i.e., after all transforms,
  // except for the prelude of the frontend, together with the messages of all errors that are reported
  def output(args: String*): (List[Cmd], List[String]) =
    show(args)
    val buffer = mutable.ListBuffer[Cmd]()
    val (_, results) = Cuvee.run(args.toList, List(Sink.collect(buffer)))
    (buffer.toList.filterNot(prelude(args*).contains), results.collect { case error: Error => error.msg })

  // the commands that the stages pass on, before the declarations known to the receiver are dropped (see Cuvee.pipe),
  // e.g. the lemma database injected by -teq, with the messages of the errors that are reported
  def stream(args: String*): (List[Cmd], List[String]) =
    show(args)
    val config = cuvee.Config.parse(cuvee.Config.default, args.toList)
    cuvee.core.Var.reset()
    cuvee.core.Param.reset()
    val (init, cmds) = config.input.source(config, config.reader)
    val buffer = mutable.ListBuffer[Cmd]()
    val report = cuvee.pipe.Report.stream(new java.io.PrintStream(java.io.OutputStream.nullOutputStream), config.input.printer)
    val (_, _, results) = cuvee.pipe.Pipe.run(cmds #::: LazyList(cuvee.core.Done), config.stages(init, Sink.collect(buffer)), report, incremental = false)
    (buffer.toList, results.collect { case error: Error => error.msg })

  // the commands of the prelude of the frontend of the input file in `args`
  def prelude(args: String*): List[Cmd] =
    val config = cuvee.Config.parse(cuvee.Config.default, args.toList)
    val (_, cmds) = config.input.source(config, new java.io.StringReader(""))
    cmds.toList

  // runs Cuvee on `args` and returns the parsed input commands, without the prelude of the frontend
  def input(args: String*): List[Cmd] =
    show(args)
    val (cmds, _) = Cuvee.run(args*)
    cmds.filterNot(prelude(args*).contains)

  // the examples below `dir` with the extension `ext`, each a test of the command line in its first line,
  // which is printed (see cuvee.test.Expected)
  def checked(dir: os.SubPath, ext: String): Tests =
    checked(find(dir, ext))

  def checked(files: List[os.Path]): Tests =
    // the expected outputs are named after the example without its extension, which must be unique
    val clashes = files.groupBy(file => file / os.up / file.baseName).filter(_._2.length > 1).keys
    assert(clashes.isEmpty, "examples whose expected outputs clash: " + clashes.mkString(", "))
    tests(files): file =>
      println("./Cuvee.sh -test " + file.relativeTo(workspace))
      cuvee.test.Expected.check(workspace.toNIO, file.toNIO).mkString("\n") ==> ""
