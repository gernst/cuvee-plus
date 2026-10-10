package cuvee.test

import utest._

import cuvee.Config

// -include injects a file of the user after the prelude, parsed in the language of its extension, such that the input
// can refer to its declarations if it is in the same language, and the output contains them; the input is given as
// text, the included file by its absolute path, since the tests run in the sandbox of mill, not in the repository
object Include extends TestSuite:
  val tests = Tests:
    test("dafny"):
      val included = Examples.root / "dafny" / "parsing" / "include_definitions.dfy"
      val config = Config.parse(Config.default, List("-include", included.toString, "input.dfy"))
      val (_, cmds) = config.input.source(config, new java.io.StringReader("lemma twice(x: int) ensures double(x) == x + x"))
      val output = config.output.printer.lines(cmds.toList.filterNot(Examples.prelude("input.dfy").contains))
      output.mkString("\n").trim ==>
        """function double(x: int): int {
          |  2 * x
          |}
          |
          |lemma twice(x: int)
          |  ensures double(x) == x + x""".stripMargin
