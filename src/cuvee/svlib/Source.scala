package cuvee.svlib

import java.io.Reader

import cuvee.Config
import cuvee.core.Cmd
import cuvee.core.State
import cuvee.pipe.Scanner

// SV-LIB scripts are SMT-LIB scripts, whose parser reads the programs of SV-LIB (see smtlib.Parser.procedure),
// and start from its prelude
object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader): Scanner =
    new cuvee.sexpr.Scanner(reader)

  def newParser(config: Config): (State, easyparse.Parser[List[Cmd]], List[Cmd]) =
    val parser = new cuvee.smtlib.Parser(State.empty)
    val lifted = cuvee.smtlib.Source.lift(parser)

    val prelude = parse("/cuvee/smtlib/prelude.smt2", lifted)

    // the parser's state now contains the declarations of the prelude
    parser.resetPoint()
    (parser.state, lifted, prelude)

  // no further definitions
  def preludes(config: Config): List[String] =
    Nil
