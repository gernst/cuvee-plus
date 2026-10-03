package cuvee.pipe

import java.io.PrintStream

import cuvee.Error
import cuvee.core._
import java.io.FileOutputStream

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
  def stdout(printer: Printer) =
    Print(System.out, printer)

  def stderr(printer: Printer) =
    Print(System.err, printer)

  def file(name: String)(printer: Printer) =
    val stream = new PrintStream(new FileOutputStream(name))
    Print(stream, printer)

  def tee(primary: Sink, secondary: Sink*) =
    Tee(primary, secondary.toList)

  class Print(stream: PrintStream, printer: Printer) extends Sink:
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

        // no information is available when printing only
        case _: GetInfo | _: GetOption =>
          (Ack.Unsupported, this)

        case GetModel =>
          Error.raise("no model available")

        case Labels =>
          Error.raise("no labels available")

  class Tee(primary: Sink, secondary: List[Sink]) extends Sink:
    def query(cmd: Cmd) =
      val secondary_ =
        for sink <- secondary
        yield
          val (_, sink_) = sink.query(cmd)
          sink_

      val (res, primary_) = primary.query(cmd)
      (res, Tee(primary_, secondary_))