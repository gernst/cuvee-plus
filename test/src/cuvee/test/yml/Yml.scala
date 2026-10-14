package cuvee.test
package yml

import scala.jdk.CollectionConverters._

import utest._

import cuvee.core._
import cuvee.yml.Task
import cuvee.Cuvee

// SV-COMP task definitions defer to the C frontend for their single input file, relative to the task
object Tasks extends TestSuite:
  def task(file: os.Path) =
    val reader = new java.io.FileReader(file.toIO)
    try Task.load(reader)
    finally reader.close()

  def input(file: os.Path) =
    file / os.up / os.RelPath(task(file).input)

  val tests =
    Examples.tests(Examples.valid(os.sub / "yml", "yml")): file =>
      // the same commands as for the input file
      Examples.show(List("-print", "null", file.toString))
      val (cmds, _) = Cuvee.run("-print", "null", file.toString)
      Examples.show(List("-print", "null", input(file).toString))
      val (cmds_, _) = Cuvee.run("-print", "null", input(file).toString)
      cmds ==> cmds_

      // the expected verdict of the property
      val List(prop) = task(file).properties: @unchecked
      Examples.show(List("-simplify", "-chc", "-z3", file.toString))
      val (_, results) = Cuvee.run("-simplify", "-chc", "-z3", file.toString)
      Examples.status(results) ==> (if prop.expected == Some(true) then Status.Sat else Status.Unsat)

// the task definition is read with SnakeYAML, the input files may be a single string or a list
// (see examples/yml/parsing for the errors)
object Load extends TestSuite:
  def load(text: String) =
    Task.load(new java.io.StringReader(text))


  val tests = Tests:
    test("task"):
      val text = "input_files: [a.c]\nproperties:\n  - property_file: p.prp\n    expected_verdict: false\n    subproperty: valid-deref\n"
      load(text) ==> Task("a.c", List(cuvee.yml.Property("p.prp", Some(false), Some("valid-deref"))), "C", None)
      load("input_files: a.c\noptions:\n  data_model: LP64\n") ==> Task("a.c", Nil, "C", Some("LP64"))

// the witnesses of SV-COMP (format 2.0) for the answers of -verify to C programs, without content for now, at a
// fixed identifier and time, since the command line writes them to a file with a fresh one (see yml.Witness)
object Witnesses extends TestSuite:
  import cuvee.yml.Witness
  import cuvee.yml.Program

  val program = Program("a.c", "00ff", "ILP32")
  val uuid = java.util.UUID.fromString("c66c3ee7-e0de-4bae-87f0-fd48fc7b961d")
  val time = java.time.OffsetDateTime.parse("2026-10-14T10:00:23.5+02:00")

  def load(text: String) =
    org.snakeyaml.engine.v2.api.Load(org.snakeyaml.engine.v2.api.LoadSettings.builder().build()).loadFromString(text)

  // the single entry of a witness, as nested Java maps and lists turned into strings for comparison
  def entry(status: Status) =
    val Some(text) = Witness.witness(program, status, uuid, time): @unchecked
    val List(entry) = load(text).asInstanceOf[java.util.List[?]].asScala.toList: @unchecked
    entry.asInstanceOf[java.util.Map[String, Any]].asScala

  val tests = Tests:
    test("correctness"):
      val e = entry(Status.Correct)
      e("entry_type") ==> "invariant_set"
      e("content").toString ==> "[]"
      e("metadata").toString ==>
        "{format_version=2.0, uuid=c66c3ee7-e0de-4bae-87f0-fd48fc7b961d, creation_time=2026-10-14T10:00:23+02:00, " +
        "producer={name=Cuvée, version=" + cuvee.Config.release + "}, task={input_files=[a.c], input_file_hashes={a.c=00ff}, " +
        "specification=G ! call(reach_error()), data_model=ILP32, language=C}}"

    test("violation"):
      val e = entry(Status.Incorrect)
      e("entry_type") ==> "violation_sequence"
      e("content").toString ==> "[]"

    test("unknown"):
      Witness.witness(program, Status.Unknown, uuid, time) ==> None

    // the strings are quoted, so that readers of YAML 1.1 take the creation time for a string
    test("quoted"):
      val Some(text) = Witness.witness(program, Status.Correct, uuid, time): @unchecked
      assert(text.contains("\"creation_time\": \"2026-10-14T10:00:23+02:00\""))

    // the input file of a task relative to the task definition, its data model from the task
    test("task"):
      val task = Examples.root / "yml" / "parsing" / "ilp32.yml"
      val Some(p) = Witness.program(cuvee.Config.parse(cuvee.Config.default, List(task.toString))): @unchecked
      p.name ==> (task / os.up / "long.c").toString
      p.model ==> "ILP32"
      p.hash.length ==> 64

    // SV-LIB has witnesses of its own, the format of C does not apply
    test("svlib"):
      val script = Examples.root / "svlib" / "horn" / "loop_add.svlib"
      Witness.program(cuvee.Config.parse(cuvee.Config.default, List(script.toString))) ==> None
