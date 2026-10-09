package cuvee.smtlib

import java.io.Reader

import cuvee.Config
import cuvee.core.Cmd
import cuvee.core.State
import cuvee.pipe.Scanner
import cuvee.sexpr.Grammar

object Source extends cuvee.pipe.Source:
  def newScanner(reader: Reader): Scanner =
    new cuvee.sexpr.Scanner(reader)

  // each s-expression is one command
  def lift(parser: Parser) =
    Grammar.sexpr.map(from => List(parser.cmd(from)))

  // the input is parsed starting from the predefined sorts and functions,
  // which is also the state that reset returns to
  def newParser(config: Config): (State, easyparse.Parser[List[Cmd]], List[Cmd]) =
    val parser = new Parser(State.empty)
    val lifted = lift(parser)

    val prelude = parse("/cuvee/smtlib/prelude.smt2", lifted)

    // the parser's state now contains the declarations of the prelude
    parser.resetPoint()
    (parser.state, lifted, prelude)

  // no further definitions
  def preludes(config: Config): List[String] =
    Nil
