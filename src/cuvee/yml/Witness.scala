package cuvee.yml

import java.io.File
import java.io.FileReader
import java.io.PrintStream
import java.nio.file.Files
import java.security.MessageDigest
import java.time.OffsetDateTime
import java.time.format.DateTimeFormatter
import java.time.temporal.ChronoUnit
import java.util.UUID

import scala.jdk.CollectionConverters._

import org.snakeyaml.engine.v2.api.Dump
import org.snakeyaml.engine.v2.api.DumpSettings
import org.snakeyaml.engine.v2.api.RepresentToNode
import org.snakeyaml.engine.v2.common.FlowStyle
import org.snakeyaml.engine.v2.common.ScalarStyle
import org.snakeyaml.engine.v2.nodes.Tag
import org.snakeyaml.engine.v2.representer.StandardRepresenter

import easyparse.Token

import cuvee.Config
import cuvee.Lang
import cuvee.core._
import cuvee.pipe.Report

// the program of a witness: its input file as given on the command line or in the task definition, the SHA-256 of
// its contents, its data model, ILP32 or LP64, and the lines and columns of the calls of reach_error (see targets)
case class Program(name: String, hash: String, model: String, targets: List[(Int, Int)])

// the verification witnesses of SV-COMP (format 2.0, https://gitlab.com/sosy-lab/benchmarking/sv-witnesses) for the
// answers to a C program: correct gives a correctness witness without invariants, which leaves the proof
// to the validator, incorrect a violation witness whose single segment is the target, the call of reach_error, which
// leaves the search for the path to the validator, if the program has exactly one call, otherwise none, since the
// failing assertion is not known (see ideas/witnesses.md)
object Witness:
  // the property of SV-COMP that the answers to C programs decide
  val specification = "G ! call(reach_error())"

  // the functions whose calls violate the specification, as in c.Parser
  val errors = Set("reach_error", "__VERIFIER_error")

  // writes the witness for the answer to the end of the input, if it is correct or incorrect, to `file`
  def report(config: Config, file: String, next: Report) =
    Witnessing(config, file, next)

  // the program of the configuration, for C input or an SV-COMP task whose input file is C, otherwise none, e.g.
  // SV-LIB, whose witnesses are part of the language; the languages are told apart by their sources, since the
  // transforms add features to them, e.g. teq by -teq (see Config.having)
  def program(config: Config): Option[Program] =
    config.file match
      case Some(file) if config.input.source == cuvee.c.Source =>
        Some(program(new File(file), file, config.arch))

      case Some(file) if config.input.source == Source =>
        val (task, input) = Source.load(file)
        if Source.lang(task).source != cuvee.c.Source
        then None
        else
          // the input file relative to the task definition as given, as for a validator that is given the task
          val name = if new File(task.input).isAbsolute then task.input else new File(new File(file).getParent, task.input).getPath
          val arch = task.model.map(model => if model == "ILP32" then 32 else 64).getOrElse(config.arch)
          Some(program(input, name, arch))

      case _ =>
        None

  def program(input: File, name: String, arch: Int): Program =
    val digest = MessageDigest.getInstance("SHA-256").digest(Files.readAllBytes(input.toPath))
    val hash = digest.map(b => "%02x".format(b)).mkString
    Program(name, hash, if arch == 32 then "ILP32" else "LP64", targets(input))

  // the lines and columns of the calls of the error functions in `file`, whose names the C scanner locates, e.g.
  // reach_error(); in the body of __VERIFIER_assert, but not their declarations and definitions, void reach_error(),
  // nor the name in a string, e.g. of __assert_fail
  def targets(file: File): List[(Int, Int)] =
    val reader = new FileReader(file)
    try
      val tokens = new cuvee.c.Scanner(reader).input.toList
      val calls =
        for case List(prev, Token.Located("sym", name, line, column), Token.Keyword("(")) <- tokens.sliding(3)
            if errors.contains(name) && prev != Token.Keyword("void")
        yield (line, column)
      calls.toList
    finally reader.close()

  // the metadata of a witness of `program` with the identifier `uuid`, created at `time`
  def metadata(program: Program, uuid: UUID, time: OffsetDateTime) =
    map(
      "format_version" -> "2.0",
      "uuid" -> uuid.toString,
      "creation_time" -> time.truncatedTo(ChronoUnit.SECONDS).format(DateTimeFormatter.ISO_OFFSET_DATE_TIME),
      "producer" -> map("name" -> "Cuvée", "version" -> Config.release),
      "task" -> map(
        "input_files" -> list(program.name),
        "input_file_hashes" -> map(program.name -> program.hash),
        "specification" -> specification,
        "data_model" -> program.model,
        "language" -> "C"
      )
    )

  // the correctness witness, an invariant set without invariants
  def correctness(program: Program, uuid: UUID, time: OffsetDateTime): String =
    dump(list(map("entry_type" -> "invariant_set", "metadata" -> metadata(program, uuid, time), "content" -> list())))

  // the violation witness with a single segment, whose waypoint is the target at `line` and `column`
  def violation(program: Program, line: Int, column: Int, uuid: UUID, time: OffsetDateTime): String =
    val location = map("file_name" -> program.name, "line" -> Int.box(line), "column" -> Int.box(column))
    val target = map("waypoint" -> map("type" -> "target", "action" -> "follow", "location" -> location))
    val content = list(map("segment" -> list(target)))
    dump(list(map("entry_type" -> "violation_sequence", "metadata" -> metadata(program, uuid, time), "content" -> content)))

  // the witness for `status`, none for unknown, and for incorrect unless the program has exactly one target
  def witness(program: Program, status: Status, uuid: UUID, time: OffsetDateTime): Option[String] =
    (status, program.targets) match
      case (Status.Correct, _)                      => Some(correctness(program, uuid, time))
      case (Status.Incorrect, List((line, column))) => Some(violation(program, line, column, uuid, time))
      case _                                        => None

  // the keys in order, as the format lists them
  def map(entries: (String, Any)*): java.util.Map[String, Any] =
    val m = new java.util.LinkedHashMap[String, Any]()
    for (key, value) <- entries do m.put(key, value)
    m

  def list(items: Any*): java.util.List[Any] =
    items.toList.asJava

  def dump(doc: Any): String =
    val settings = DumpSettings.builder().setDefaultFlowStyle(FlowStyle.BLOCK).build()
    Dump(settings, Quoting(settings)).dumpToString(doc)

// the strings in double quotes, as other tools write them, since a reader of YAML 1.1 such as PyYAML takes the
// creation time for a date otherwise, where the format has a string; the numbers plain, e.g. the lines of locations
class Quoting(settings: DumpSettings) extends StandardRepresenter(settings):
  representers.put(
    classOf[String],
    new RepresentToNode:
      def representData(data: Any) = representScalar(Tag.STR, data.toString, ScalarStyle.DOUBLE_QUOTED)
  )

// passes the reports to `next`, and writes the witness for the answer to the input at the end of the run: incorrect if
// one of the reported answers is, correct if there is one and all are, otherwise unknown, for which there is none
case class Witnessing(config: Config, file: String, next: Report) extends Report:
  val answers = scala.collection.mutable.ListBuffer[Status]()

  def report(result: Result, printSuccess: Boolean) =
    result match
      case answer @ (Status.Correct | Status.Incorrect | Status.Unknown) => answers += answer
      case _                                                             =>
    next.report(result, printSuccess)

  override def done() =
    val status =
      if answers.contains(Status.Incorrect) then Status.Incorrect
      else if answers.nonEmpty && answers.forall(_ == Status.Correct) then Status.Correct
      else Status.Unknown

    for
      program <- Witness.program(config)
      text <- Witness.witness(program, status, UUID.randomUUID(), OffsetDateTime.now())
    do
      val out = new PrintStream(file, "UTF-8")
      try out.print(text)
      finally out.close()

    next.done()
