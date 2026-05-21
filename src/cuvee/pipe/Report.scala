package cuvee.pipe

import java.io.PrintStream

import cuvee.core._

trait Report:
  def report(result: Result, printSuccess: Boolean): Unit

object Report:
  def stdout(printer: cuvee.Printer) =
    new print(System.out, printer)

  def stderr(printer: cuvee.Printer) =
    new print(System.err, printer)

  class print(stream: PrintStream, printer: cuvee.Printer) extends Report:
    def report(result: Result, printSuccess: Boolean) =
      result match
        case ack: Ack if !printSuccess =>
        // suppressed response

        case _ =>
          for (line <- printer.lines(result))
            stream.println(line)
