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

    val reader = resource("/cuvee/dafny/builtin.dfy")
    try cmds(newScanner(reader).input, lifted).force
    finally reader.close()

    // the parser's state now contains the built-in declarations
    (parser.state, lifted)

  // tuples, and with -hybrid, the definitions of parallel composition
  override def preludes(config: cuvee.Config) =
    if config.hybrid
    then List("/cuvee/dafny/prelude.dfy", "/cuvee/dafny/hybrid.dfy")
    else List("/cuvee/dafny/prelude.dfy")
