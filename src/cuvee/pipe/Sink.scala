package cuvee.pipe

import java.io.PrintStream
import scala.collection.mutable

import cuvee.Error
import cuvee.core._
import java.io.FileOutputStream

// the answer to a command, and separately the answers that a flush brings: those to the obligations that a stage
// buffered before it, and to the queries that transforms add in front of it, e.g. check-sat and get-model added at
// the end of the input (see Stage), which are reported before the answer to the command (see Pipe.run)
trait Sink:
  def query(cmd: Cmd): (Result, List[Result], Sink)

  // the features of the declarations that the receiver of the commands knows already, which are dropped before it
  // (see Sink.filter and Cuvee.pipe), e.g. the prelude of the language of the output for a printer
  def knows: Set[String] =
    Set()

  // the answers to the commands `cmds`, i.e. to the goals and lemmas, which every sink answers, and to the queries,
  // also none (Ack.Done), which Pipe.run does not report, together with the answers that they bring, e.g. those to the goals of procedures that a stage passes on in front of a goal (see
  // Stage.query); free lemmas are not among them, they are acknowledged like axioms
  def query(cmds: List[Cmd]): (List[Result], Sink) =
    cmds match
      case Nil =>
        (Nil, this)

      case cmd :: rest =>
        val (result, added, sink) = query(cmd)
        val answers =
          cmd match
            case Assert(Goal | Lemma, _, _, attrs) if !attrs.contains("free") => added :+ result
            case _: Query                                                    => added :+ result
            case _                                                           => added
        val (answers_, sink_) = sink.query(rest)
        (answers ++ answers_, sink_)

  // the answer to `last`, and the answers to the commands among `cmds` and those that `last` brings
  def query(cmds: List[Cmd], last: Cmd): (Result, List[Result], Sink) =
    val (answers, sink) = query(cmds)
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

  // drops the declarations whose features the receiver knows, which it acknowledges like a printer, except that a goal
  // or lemma that is not free is unknown, since nobody checks it
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

  // the answer of sinks that only pass on commands without solving: a goal or lemma is decided by its form, true
  // correct and false incorrect, unless it is :abstract (see Solver.sink), and unknown otherwise, such that every one
  // that reaches a sink is answered; a free lemma, which is assumed, is acknowledged like an axiom
  def passive(cmd: Cmd): Result =
    cmd match
      case Assert(Lemma, _, _, attrs) if attrs.contains("free") =>
        Ack.Success

      case Assert(Goal | Lemma, _, True, _) =>
        Status.Correct

      case Assert(Goal | Lemma, _, False, attrs) if attrs.contains("abstract") =>
        Status.Unknown

      case Assert(Goal | Lemma, _, False, _) =>
        Status.Incorrect

      case Assert(Goal | Lemma, _, _, _) =>
        Status.Unknown

      case _: Decl =>
        Ack.Success

      case Done =>
        Ack.Done

      case _: Ctrl =>
        Ack.Success

      case CheckSat =>
        Status.Unknown

      // no information is available when printing only, and no witnesses are produced
      case _: GetInfo | _: GetOption | GetWitness =>
        Ack.Unsupported

      // no answer, e.g. to the get-model added by Horn
      case GetModel =>
        Ack.Done

      // no answer of its own, the goals generated for the procedures are answered
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
      then
        cmd match
          case Assert(Goal | Lemma, _, _, attrs) if !attrs.contains("free") => (Status.Unknown, Nil, this)
          case _                                                           => (Ack.Success, Nil, this)
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
