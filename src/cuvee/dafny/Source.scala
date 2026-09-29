package cuvee.dafny

import java.io.Reader

import cuvee.core.State
import java.io.FileReader

object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Scanner(reader)

  def newParser() =
    val parser = new Parser(State.empty)

    val lifted =
      for
        cmd <- Grammar.cmd;
        cmd_ <- parser.resolve(cmd)
      yield cmd_

    val reader = new FileReader("src/cuvee/dafny/prelude.dfy")
    val scanner = newScanner(reader)
    val prelude = cmds(scanner.input, lifted)
    prelude.force

    lifted
