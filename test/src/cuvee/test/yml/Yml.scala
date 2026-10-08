package cuvee.test
package yml

import utest._

import cuvee.core._
import cuvee.yml.Task

// the examples in yml, each with its command line in the first line, among them the cases of the frontend in yml/parsing
object Checked extends TestSuite:
  val tests =
    Examples.checked(os.sub / "yml", "yml")

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
      val (cmds, _) = cuvee.Cuvee.run("-print", "null", file.toString)
      Examples.show(List("-print", "null", input(file).toString))
      val (cmds_, _) = cuvee.Cuvee.run("-print", "null", input(file).toString)
      cmds ==> cmds_

      // the expected verdict of the property
      val List(prop) = task(file).properties: @unchecked
      Examples.show(List("-simplify", "-chc", "-z3", file.toString))
      val (_, results) = cuvee.Cuvee.run("-simplify", "-chc", "-z3", file.toString)
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
