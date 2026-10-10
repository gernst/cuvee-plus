package cuvee.test

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters._

import cuvee.Error

// a database of the expected results of many examples in a single CSV file, instead of name.out and name.err next to
// each, for the translations of SV-COMP tasks (benchmarks/sv-comp/dafny/expected.csv): each row is an example with its
// command line in its first line, whether its task is safe or unsafe, and the number of goals that remain,
// or error if the run reports an error or crashes; the lemmas of the examples are marked {:teq}, such that they are
// not printed, and only goals are counted;
// the C programs printed from them (benchmarks/sv-comp/c/expected.csv) have their command line and task in their
// first two lines, too;
// SV-COMP task definitions (.yml) themselves have no command line, they are run with -teq -simplify through the C
// frontend (benchmarks/sv-comp/dafny/yml.csv); rows whose goals are timeout record runs that did not end within the time
// limit of a run by hand, which cannot be enforced in the same JVM, they are not checked;
// the time of each run in milliseconds is recorded, too, a run that takes more than 110% of it or less than 10% of it,
// with a slack of a second for the noise of runs in the same JVM, is a failure: a slower run is a performance
// degradation, a run that ends much faster is likely a soundness bug, e.g. goals that are closed by mistake; rows
// without a time are not timed
//   ./Cuvee.sh -record <file> ... > expected.csv   writes the database of the examples (by hand, tests never write)
//   ./Cuvee.sh -test expected.csv                  checks all rows
object Database:
  case class Row(file: String, verdict: String, goals: String, time: Option[Long])

  val header = "file,verdict,goals,time"

  // the task definition named in the header of an example, "SV-COMP <folder>/<task>.yml", below sv-benchmarks/c/,
  // whose expected verdict for the property unreach-call is safe (true) or unsafe (false)
  // of a task definition itself, its own verdict
  def verdict(root: Path, file: Path): String =
    val text = Files.readString(file).replace("\n// ", " ")
    val yml =
      if file.toString.endsWith(".yml")
      then Some(file)
      else
        for
          m <- "SV-COMP (\\S+\\.yml)".r.findFirstMatchIn(text)
          yml = root.resolve("sv-benchmarks").resolve("c").resolve(m.group(1))
          if Files.exists(yml)
        yield yml
    val verdict =
      for
        yml <- yml
        v <- "unreach-call\\.prp\\s*\\n\\s*expected_verdict:\\s*(\\w+)".r.findFirstMatchIn(Files.readString(yml))
      yield v.group(1)

    verdict match
      case Some("true")  => "safe"
      case Some("false") => "unsafe"
      case _             => "unknown"

  // the command line of an example, without ./Cuvee.sh, in its first line, or -teq -simplify for a task definition
  def command(root: Path, file: Path): Option[List[String]] =
    if file.toString.endsWith(".yml")
    then Some(List("-teq", "-simplify", root.relativize(file).toString))
    else Expected.command(root, file)

  // runs the example `file` below `root` with its command line
  def record(root: Path, file: Path): Row =
    val path = root.relativize(file).toString
    val start = System.nanoTime
    val goals =
      command(root, file) match
        case None =>
          "error"

        case Some(args) =>
          try
            val (out, err, _) = Expected.run(args, file)
            // goals and errors in Dafny, or in SMT-LIB, the output of C input
            if (out ++ err).exists(line => line.startsWith("error") || line.startsWith("(error"))
            then "error"
            else out.count(line => line.startsWith("goal") || line.startsWith("(goal")).toString
          catch case _: Throwable => "error"

    val time = (System.nanoTime - start) / 1000000
    Row(path, verdict(root, file), goals, Some(time))

  // a run that is slower than 110% of the expected time or faster than 10% of it, with a slack of a second each
  def timely(expected: Long, actual: Long): Option[String] =
    if actual > expected * 11 / 10 + 1000
    then Some(s"slower: expected $expected ms, actual $actual ms")
    else if actual < expected / 10 - 1000
    then Some(s"faster: expected $expected ms, actual $actual ms")
    else None

  // the difference of the run of a row to the row, if any, and the run
  def check(root: Path, row: Row): (Option[String], Row) =
    val actual = record(root, root.resolve(row.file))
    val results =
      if actual.verdict != row.verdict || actual.goals != row.goals
      then Some(s"expected ${row.verdict} with ${row.goals} goals, actual ${actual.verdict} with ${actual.goals} goals")
      else None
    val times =
      for
        expected <- row.time
        actual <- actual.time
        diff <- timely(expected, actual)
      yield diff
    (List(results, times).flatten.reduceOption(_ + "; " + _), actual)

  // the differences of the runs of the rows to the rows, none if all match
  def check(root: Path, rows: List[Row]): List[String] =
    for
      row <- rows
      if row.goals != "timeout"
      diff <- check(root, row)._1
    yield s"${row.file}: $diff"

  def read(file: Path): List[Row] =
    val lines = Files.readAllLines(file).asScala.toList
    assert(lines.headOption.exists(line => line == header || line == "file,verdict,goals"), "not a database of expected results: " + file)
    for line <- lines.tail
    yield line.split(",").toList match
      case List(file, verdict, goals, time) => Row(file, verdict, goals, time.toLongOption)
      case List(file, verdict, goals)       => Row(file, verdict, goals, None)
      case _                                => Error.raise("not a row of the database", line)

  // ./Cuvee.sh -record <file> ...: prints the database of the examples
  def main(files: List[String]): Int =
    val root = Path.of("").toAbsolutePath
    println(header)
    for file <- files
    do
      val Row(path, verdict, goals, time) = record(root, root.resolve(file).normalize)
      println(s"$path,$verdict,$goals,${time.getOrElse("")}")
    0

  // ./Cuvee.sh -test <database>.csv: prints each row as it is checked, with the differences, and a summary,
  // returns 0 if all rows match
  def test(file: String): Int =
    val root = Path.of("").toAbsolutePath
    val rows = read(root.resolve(file))
    var failed = 0
    for (row, i) <- rows.zipWithIndex if row.goals != "timeout"
    do
      val (diff, actual) = check(root, row)
      val time = actual.time.getOrElse(0L) + " ms"
      diff match
        case None =>
          println(s"[${i + 1}/${rows.length}] ok ${row.file} ($time)")
        case Some(diff) =>
          failed += 1
          println(s"[${i + 1}/${rows.length}] failed ${row.file}: $diff")
    println((if failed == 0 then "ok " else s"failed $failed of ") + file + ", " + rows.length + " examples")
    if failed == 0 then 0 else 1
