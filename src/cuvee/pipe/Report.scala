package cuvee.pipe

import java.io.PrintStream
import scala.collection.mutable

import cuvee.core._

trait Report:
  def report(result: Result, printSuccess: Boolean): Unit

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

  class collect(buffer: mutable.ListBuffer[Result]) extends Report:
    def report(result: Result, printSuccess: Boolean) =
      result match
        case ack: Ack if !printSuccess =>
        // suppressed response

        case _ =>
          buffer.append(result)
