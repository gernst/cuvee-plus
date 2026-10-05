package cuvee.dafny

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

    val prelude = parse("/cuvee/dafny/prelude.dfy", lifted)

    // the parser's state now contains the declarations of the prelude
    (parser.state, lifted, prelude)

  // with -hybrid, the definitions of parallel composition
  override def preludes(config: cuvee.Config) =
    if config.hybrid
    then List("/cuvee/dafny/hybrid.dfy")
    else Nil
