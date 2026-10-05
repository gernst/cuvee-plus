package cuvee.boogie

import java.io.Reader

import cuvee.core.State

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

    val prelude = parse("/cuvee/boogie/prelude.bpl", lifted)

    // the parser's state now contains the declarations of the prelude
    (parser.state, lifted, prelude)
