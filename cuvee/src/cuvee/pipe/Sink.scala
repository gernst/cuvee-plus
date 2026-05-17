package cuvee.pipe

import cuvee.smtlib._

trait Sink:
  def query(cmd: Cmd): (Result, Sink)

  def query(cmds: List[Cmd], last: Cmd): (Result, Sink) =
    exec(cmds).query(last)

  def exec(cmd: Cmd) =
    val (result, sink) = query(cmd)
    sink

  def exec(cmds: List[Cmd]): Sink =
    cmds match
      case Nil =>
        this

      case first :: rest =>
        exec(first).exec(rest)
