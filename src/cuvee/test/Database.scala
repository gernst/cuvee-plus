package cuvee.test

import java.nio.file.Files
import java.nio.file.Path
import scala.jdk.CollectionConverters._

// a database of the expected results of many examples in a single CSV file, instead of name.out and name.err next to
// each, for the translations of SV-COMP tasks (examples/sv-comp/expected.csv): each row is an example with its
// command line in its first line, whether its task is safe or unsafe, and the number of goals that remain,
// or error if the run reports an error or crashes; the lemmas of the examples are marked {:teq}, such that they are
// not printed, and only goals are counted;
// SV-COMP task definitions (.yml) themselves have no command line, they are run with -teq -simplify through the C
// frontend (examples/sv-comp/yml.csv); rows whose goals are timeout record runs that did not end within the time
// limit of a run by hand, which cannot be enforced in the same JVM, they are not checked
//   ./Cuvee.sh -record <file> ... > expected.csv   writes the database of the examples (by hand, tests never write)
//   ./Cuvee.sh -test expected.csv                  checks all rows
object Database:
  case class Row(file: String, verdict: String, goals: String)

  val header = "file,verdict,goals"

  // the task definition named in the header of an example, "SV-COMP <folder>/<task>.yml", below benchmarks/,
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
          yml = root.resolve("benchmarks").resolve(m.group(1))
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

    Row(path, verdict(root, file), goals)

  // the differences of the run of each row to the row, none if all match
  def check(root: Path, rows: List[Row]): List[String] =
    for
      row <- rows
      if row.goals != "timeout"
      actual = record(root, root.resolve(row.file))
      if actual != row
    yield s"${row.file}: expected ${row.verdict} with ${row.goals} goals, actual ${actual.verdict} with ${actual.goals} goals"

  def read(file: Path): List[Row] =
    val lines = Files.readAllLines(file).asScala.toList
    assert(lines.headOption.contains(header), "not a database of expected results: " + file)
    for case s"$file,$verdict,$goals" <- lines.tail
    yield Row(file, verdict, goals)

  // ./Cuvee.sh -record <file> ...: prints the database of the examples
  def main(files: List[String]): Int =
    val root = Path.of("").toAbsolutePath
    println(header)
    for file <- files
    do
      val Row(path, verdict, goals) = record(root, root.resolve(file).normalize)
      println(s"$path,$verdict,$goals")
    0

  // ./Cuvee.sh -test <database>.csv: prints the differences and a summary, returns 0 if all rows match
  def test(file: String): Int =
    val root = Path.of("").toAbsolutePath
    val rows = read(root.resolve(file))
    val diffs = check(root, rows)
    diffs.foreach(println)
    println((if diffs.isEmpty then "ok " else "failed ") + file + ", " + rows.length + " examples")
    if diffs.isEmpty then 0 else 1
