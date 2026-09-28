package cuvee.dafny

import java.io.Reader

import cuvee.core.State

object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader) =
    new Scanner(reader)

  def newParser() =
    val parser = new Parser(State.empty)

    for
      cmd <- Grammar.cmd;
      cmd_ <- parser.resolve(cmd)
    yield cmd_
