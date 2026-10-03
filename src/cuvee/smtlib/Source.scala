package cuvee.smtlib

import java.io.Reader

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
  def newParser(): (State, easyparse.Parser[List[Cmd]]) =
    val prelude = new Parser(State.empty)
    val reader = resource("/cuvee/smtlib/prelude.smt2")
    try cmds(newScanner(reader).input, lift(prelude)).force
    finally reader.close()

    val init = prelude.state
    val parser = new Parser(init)
    (init, lift(parser))
