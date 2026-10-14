package cuvee.yml

import java.io.File
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
import org.snakeyaml.engine.v2.common.FlowStyle
import org.snakeyaml.engine.v2.common.ScalarStyle

import cuvee.Config
import cuvee.Lang
import cuvee.core._
import cuvee.pipe.Sink

// the program of a witness: its input file as given on the command line or in the task definition, the SHA-256 of
// its contents, and its data model, ILP32 or LP64
case class Program(name: String, hash: String, model: String)

// the verification witnesses of SV-COMP (format 2.0, https://gitlab.com/sosy-lab/benchmarking/sv-witnesses) for the
// answer of -verify to a C program, both without content for now: correct gives a correctness witness without
// invariants, incorrect a violation witness without waypoints, which leave the proof and the search for the path to
// the validator (see ideas/witnesses.md)
object Witness:
  // the property of SV-COMP that the answers of -verify to C programs decide
  val specification = "G ! call(reach_error())"

  // writes the witness for the answer to the end of the input, if it is correct or incorrect, to `file`
  def sink(config: Config, file: String, next: Sink) =
    Witnessing(config, file, next)

  // the program of the configuration, for C input or an SV-COMP task whose input file is C, otherwise none, e.g.
  // SV-LIB, whose witnesses are part of the language
  def program(config: Config): Option[Program] =
    config.file match
      case Some(file) if config.input == Lang.c =>
        Some(program(new File(file), file, config.arch))

      case Some(file) if config.input == Lang.yml =>
        val (task, input) = Source.load(file)
        if Source.lang(task) != Lang.c
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
    Program(name, hash, if arch == 32 then "ILP32" else "LP64")

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

  // the violation witness, a violation sequence without segments
  def violation(program: Program, uuid: UUID, time: OffsetDateTime): String =
    dump(list(map("entry_type" -> "violation_sequence", "metadata" -> metadata(program, uuid, time), "content" -> list())))

  // the witness for `status`, none for unknown
  def witness(program: Program, status: Status, uuid: UUID, time: OffsetDateTime): Option[String] =
    status match
      case Status.Correct   => Some(correctness(program, uuid, time))
      case Status.Incorrect => Some(violation(program, uuid, time))
      case _                => None

  // the keys in order, as the format lists them
  def map(entries: (String, Any)*): java.util.Map[String, Any] =
    val m = new java.util.LinkedHashMap[String, Any]()
    for (key, value) <- entries do m.put(key, value)
    m

  def list(items: Any*): java.util.List[Any] =
    items.toList.asJava

  // the strings in double quotes, as other tools write them, since a reader of YAML 1.1 such as PyYAML takes the
  // creation time for a date otherwise, where the format has a string
  def dump(doc: Any): String =
    val settings = DumpSettings.builder().setDefaultFlowStyle(FlowStyle.BLOCK).setDefaultScalarStyle(ScalarStyle.DOUBLE_QUOTED).build()
    Dump(settings).dumpToString(doc)

// passes the commands to `next`, and writes the witness for its answer to the end of the input (see Verify)
case class Witnessing(config: Config, file: String, next: Sink) extends Sink:
  override def knows =
    next.knows

  def query(cmd: Cmd) =
    val (result, added, next_) = next.query(cmd)

    (cmd, result) match
      case (Done, status: Status) =>
        for
          program <- Witness.program(config)
          text <- Witness.witness(program, status, UUID.randomUUID(), OffsetDateTime.now())
        do
          val out = new PrintStream(file, "UTF-8")
          try out.print(text)
          finally out.close()

      case _ =>

    (result, added, copy(next = next_))
