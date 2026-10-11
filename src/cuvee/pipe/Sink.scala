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

  // the features of the declarations that the receiver of the commands knows already, which are dropped before it
  // (see Sink.filter and Cuvee.pipe), e.g. the prelude of the language of the output for a printer
  def knows: Set[String] =
    Set()

  // the answer to `last`, and the answers to the queries among `cmds` together with those added in front of `last`,
  // where the answers to each query follow the same rule as in Pipe.run, and queries without answer are skipped
  def query(cmds: List[Cmd], last: Cmd): (Result, List[Result], Sink) =
    val (answers, sink) =
      cmds.foldLeft((Nil: List[Result], this)):
        case ((answers, sink), cmd: Query) =>
          val (result, added, sink_) = sink.query(cmd)
          val result_ = if result == Ack.Done then answers ++ added else answers :+ result
          (result_, sink_)

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
  // the output printed to `stream`, e.g. stdout (see Config.stdout), for a receiver that knows `knows`
  def stream(stream: PrintStream, printer: Printer, knows: Set[String]) =
    Print(stream, printer, knows)

  def file(name: String, printer: Printer, knows: Set[String]) =
    Print(new PrintStream(new FileOutputStream(name)), printer, knows)

  // drops the declarations whose features the receiver knows, which it acknowledges like a printer
  def filter(features: Set[String], next: Sink) =
    Filter(features, next)

  // whether the declaration `cmd` is known to a receiver that knows `features`: the declarations of the preludes
  // (resources/cuvee/*/prelude.*) name the languages that they are part of by attributes, the file extensions smt2,
  // dfy, bpl, and c, e.g. the tuples of Dafny are part of Dafny only, and are therefore declared in SMT-LIB,
  // and those injected with -teq and -hybrid are known to the input language (see Config.having)
  def known(features: Set[String], cmd: Cmd): Boolean =
    cmd match
      case decl: Decl => features.exists(decl.attrs.contains)
      case _          => false

  def collect(buffer: mutable.ListBuffer[Cmd]) =
    Collect(buffer)

  def tee(primary: Sink, secondary: Sink*) =
    Tee(primary, secondary.toList)

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

      // no answer of its own, the answers to the obligations that the transforms add are reported instead (see Pipe.run)
      case _: VerifyCall =>
        Ack.Done

      case Labels =>
        Error.raise("no labels available")

  class Print(stream: PrintStream, printer: Printer, override val knows: Set[String]) extends Sink:
    def query(cmd: Cmd) =
      if cmd != Done then
        for (line <- printer.lines(cmd))
          stream.println(line)

      (passive(cmd), Nil, this)

  class Filter(features: Set[String], next: Sink) extends Sink:
    override def knows = next.knows

    def query(cmd: Cmd) =
      if known(features, cmd)
      then (Ack.Success, Nil, this)
      else
        val (result, added, next_) = next.query(cmd)
        (result, added, Filter(features, next_))

  // appends all commands to `buffer`, e.g. to inspect the output of transforms in tests
  class Collect(buffer: mutable.ListBuffer[Cmd]) extends Sink:
    def query(cmd: Cmd) =
      if cmd != Done then buffer.append(cmd)

      (passive(cmd), Nil, this)

  // the answers are those of the primary sink, which is the receiver
  class Tee(primary: Sink, secondary: List[Sink]) extends Sink:
    override def knows = primary.knows

    def query(cmd: Cmd) =
      val secondary_ =
        for sink <- secondary
        yield
          val (_, _, sink_) = sink.query(cmd)
          sink_

      val (result, added, primary_) = primary.query(cmd)
      (result, added, Tee(primary_, secondary_))
