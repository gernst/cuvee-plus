package cuvee.pipe

import java.io.PrintStream
import scala.collection.mutable

import cuvee.Error
import cuvee.core._
import java.io.FileOutputStream

// the answer to a command, and separately the answers to the queries that transforms add in front of it,
// e.g. check-sat and get-model added at the end of the input (see Stage),
// which are reported only if the command has no answer of its own (Ack.Done, see Pipe.run)
trait Sink:
  def query(cmd: Cmd): (Result, List[Result], Sink)

  // the answer to `last`, and the answers to the queries among `cmds` together with those added in front of `last`,
  // where the answers to each query follow the same rule as in Pipe.run, and queries without answer are skipped
  def query(cmds: List[Cmd], last: Cmd): (Result, List[Result], Sink) =
    val (answers, sink) =
      cmds.foldLeft((Nil: List[Result], this)):
        case ((answers, sink), cmd: Query) =>
          val (result, added, sink_) = sink.query(cmd)
          (if result == Ack.Done then answers ++ added else answers :+ result, sink_)

        case ((answers, sink), cmd) =>
          (answers, sink.exec(cmd))

    val (result, added, sink_) = sink.query(last)
    (result, answers ++ added, sink_)

  def exec(cmd: Cmd) =
    val (_, _, sink) = query(cmd)
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

  def filter(features: Set[String], next: Sink) =
    Filter(features, next)

  // the answer of sinks that only pass on commands without solving
  def passive(cmd: Cmd): Result =
    cmd match
      case _: Decl =>
        Ack.Success

      case Done =>
        Ack.Done

      case _: Ctrl =>
        Ack.Success

      case CheckSat =>
        Status.Unknown

      // no information is available when printing only
      case _: GetInfo | _: GetOption =>
        Ack.Unsupported

      // no answer, e.g. to the get-model added by Horn
      case GetModel =>
        Ack.Done

      case Labels =>
        Error.raise("no labels available")

  class Print(stream: PrintStream, printer: Printer) extends Sink:
    def query(cmd: Cmd) =
      if cmd != Done then
        for (line <- printer.lines(cmd))
          stream.println(line)

      (passive(cmd), Nil, this)

  // appends all commands to `buffer`, e.g. to inspect the output of transforms in tests
  class Collect(buffer: mutable.ListBuffer[Cmd]) extends Sink:
    def query(cmd: Cmd) =
      if cmd != Done then
        buffer.append(cmd)

      (passive(cmd), Nil, this)

  class Tee(primary: Sink, secondary: List[Sink]) extends Sink:
    def query(cmd: Cmd) =
      val secondary_ =
        for sink <- secondary
        yield
          val (_, _, sink_) = sink.query(cmd)
          sink_

      val (result, added, primary_) = primary.query(cmd)
      (result, added, Tee(primary_, secondary_))

  // the last step in front of each sink, which drops the declarations that its receiver knows by their features:
  // those of the preludes (resources/cuvee/*/prelude.*) name the languages that they are part of by attributes,
  // the file extensions smt2, dfy, bpl, and c, e.g. the tuples of Dafny are part of Dafny only,
  // and are therefore declared as datatypes in SMT-LIB;
  // it filters the commands in front of the sink one by one, unlike a stage, which buffers declarations,
  // such that the answers of the sink to the remaining declarations are reported, e.g. unsupported by solvers
  case class Filter(features: Set[String], next: Sink) extends Sink:
    def query(cmd: Cmd) =
      cmd match
        case decl: Decl if features.exists(decl.attrs.contains) =>
          (Ack.Success, Nil, this)

        case _ =>
          val (result, added, next_) = next.query(cmd)
          (result, added, copy(next = next_))
