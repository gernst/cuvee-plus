package cuvee.pipe

import java.io.PrintStream
import scala.collection.mutable

import cuvee.core._

trait Report:
  def report(result: Result, printSuccess: Boolean): Unit

  // the end of the run, e.g. to write the witness of the answers (see yml.Witness)
  def done(): Unit = ()

object Report:
  def stream(stream: PrintStream, printer: Printer) =
    new print(stream, printer)

  def collect(buffer: mutable.ListBuffer[Result]) =
    new collect(buffer)

  class print(stream: PrintStream, printer: Printer) extends Report:
    def report(result: Result, printSuccess: Boolean) =
      result match
        case ack: Ack if !printSuccess =>
        // suppressed response

        case _ =>
          for (line <- printer.lines(result))
            stream.println(line)

  // all results except success, which is collected only with print-success, e.g. unsupported in tests
  class collect(buffer: mutable.ListBuffer[Result]) extends Report:
    def report(result: Result, printSuccess: Boolean) =
      result match
        case Ack.Success if !printSuccess =>
        // suppressed response

        case _ =>
          buffer.append(result)
