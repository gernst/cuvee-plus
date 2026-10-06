package cuvee.test
package yml

import utest._

import cuvee.core._
import cuvee.yml.Task

// SV-COMP task definitions defer to the C frontend for their single input file, relative to the task
object Tasks extends TestSuite:
  def task(file: os.Path) =
    val reader = new java.io.FileReader(file.toIO)
    try Task.load(reader)
    finally reader.close()

  def input(file: os.Path) =
    file / os.up / os.RelPath(task(file).input)

  val tests =
    Examples.tests(Examples.find(os.sub / "yml", "yml")): file =>
      // the same commands as for the input file
      val (cmds, _) = cuvee.Cuvee.run("-print", "null", file.toString)
      val (cmds_, _) = cuvee.Cuvee.run("-print", "null", input(file).toString)
      cmds ==> cmds_

      // the expected verdict of the property
      val List(prop) = task(file).properties: @unchecked
      val (_, results) = cuvee.Cuvee.run("-chc", "-z3", file.toString)
      Examples.status(results) ==> (if prop.expected == Some(true) then Status.Sat else Status.Unsat)

// the task definition is read with SnakeYAML, the input files may be a single string or a list
object Load extends TestSuite:
  def load(text: String) =
    Task.load(new java.io.StringReader(text))

  def errors(text: String) =
    Examples.check("yml", text)

  val tests = Tests:
    test("task"):
      val text = "input_files: [a.c]\nproperties:\n  - property_file: p.prp\n    expected_verdict: false\n    subproperty: valid-deref\n"
      load(text) ==> Task("a.c", List(cuvee.yml.Property("p.prp", Some(false), Some("valid-deref"))), "C", None)
      load("input_files: a.c\noptions:\n  data_model: LP64\n") ==> Task("a.c", Nil, "C", Some("LP64"))

    test("errors"):
      errors("input_files: [a.c, b.c]\n") ==> List("only a single input file is supported")
      errors("properties: []\n") ==> List("task definition without input files")
      errors("input_files: a.c\noptions:\n  language: Java\n") ==> List("unsupported language of task")
      errors("input_files: missing.c\n") ==> List("input file of task not found")
      errors("input_files: [a.c\n") ==> List("malformed task definition")
