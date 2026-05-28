package cuvee.pipe

import cuvee.Error
import cuvee.core._
import java.io.PrintStream

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

object Sink:
  def stdout(printer: cuvee.Printer) =
    Print(System.out, printer)

  def stderr(printer: cuvee.Printer) =
    Print(System.err, printer)

  class Print(stream: PrintStream, printer: cuvee.Printer) extends Sink:
    def query(cmd: Cmd) =
      for (line <- printer.lines(cmd))
        stream.println(line)

      cmd match
        case _: Decl =>
          (Ack.Success, this)

        case _: Ctrl =>
          (Ack.Success, this)

        case CheckSat =>
          (Status.Unknown, this)

        case GetModel =>
          Error.raise("no model available")

        case Labels =>
          Error.raise("no labels available")
