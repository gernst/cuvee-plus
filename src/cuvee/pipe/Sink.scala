package cuvee.pipe

import java.io.PrintStream
import scala.collection.mutable

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

  def collect(buffer: mutable.ListBuffer[Cmd]) =
    Collect(buffer)

  def tee(primary: Sink, secondary: Sink*) =
    Tee(primary, secondary.toList)

  // the answer of sinks that only pass on commands without solving
  def passive(cmd: Cmd): Result =
    cmd match
      case _: Decl =>
        Ack.Success

      case _: Ctrl =>
        Ack.Success

      case CheckSat =>
        Status.Unknown

      // no information is available when printing only
      case _: GetInfo | _: GetOption =>
        Ack.Unsupported

      case GetModel =>
        Error.raise("no model available")

      case Labels =>
        Error.raise("no labels available")

  class Print(stream: PrintStream, printer: Printer) extends Sink:
    def query(cmd: Cmd) =
      if cmd != Done then
        for (line <- printer.lines(cmd))
          stream.println(line)

      (passive(cmd), this)

  // appends all commands to `buffer`, e.g. to inspect the output of transforms in tests
  class Collect(buffer: mutable.ListBuffer[Cmd]) extends Sink:
    def query(cmd: Cmd) =
      if cmd != Done then
        buffer.append(cmd)

      (passive(cmd), this)

  class Tee(primary: Sink, secondary: List[Sink]) extends Sink:
    def query(cmd: Cmd) =
      val secondary_ =
        for sink <- secondary
        yield
          val (_, sink_) = sink.query(cmd)
          sink_

      val (res, primary_) = primary.query(cmd)
      (res, Tee(primary_, secondary_))