package cuvee.pipe

import java.io.PrintStream

import cuvee.core._

trait Report:
  def report(result: Result, printSuccess: Boolean): Unit

object Report:
  // the reports printed to `stream`, e.g. stderr (see Config.stderr)
  def stream(stream: PrintStream, printer: Printer) =
    new print(stream, printer)

  class print(stream: PrintStream, printer: Printer) extends Report:
    def report(result: Result, printSuccess: Boolean) =
      result match
        case ack: Ack if !printSuccess =>
        // suppressed response

        case _ =>
          for (line <- printer.lines(result))
            stream.println(line)
