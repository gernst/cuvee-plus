package cuvee.pipe

import scala.util.control.Breaks

import cuvee.Error
import cuvee.core._
import cuvee.sexpr.Id

object Pipe:
  def run(source: Source, init: Sink, report: Report, incremental: Boolean) =
    var sink = init
    var printSuccess = false

    try
      Breaks.breakable:
        for cmd <- source do
          cmd match
            case SetOption("print-success", Id("true")) =>
              printSuccess = true

            case SetOption("print-success", Id("false")) =>
              printSuccess = false

            case _ =>
              try
                val (result, next) = sink.query(cmd)
                sink = next
                report.report(result, printSuccess)

                if cmd == Exit
                then Breaks.break()

              catch
                // don't catch parse errors here without advancing the input stream!
                case result: Error =>
                  report.report(result, printSuccess)

                  if (!incremental)
                    Breaks.break()

    catch
      // catches parse errors
      case result: Error =>
        report.report(result, printSuccess)
