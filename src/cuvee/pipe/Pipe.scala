package cuvee.pipe

import scala.util.control.Breaks
import scala.collection.mutable

import cuvee.Error
import cuvee.core._
import cuvee.sexpr.Id

object Pipe:
  def run(source: Iterable[Cmd], init: Sink, report: Report, incremental: Boolean) =
    var sink = init
    var printSuccess = false

    val done = mutable.ListBuffer[Cmd]()
    val results = mutable.ListBuffer[Result]()

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

                // Done is not part of the input, only errors from flushing are reported
                if cmd != Done then
                  report.report(result, printSuccess)
                  done.append(cmd)
                  results.append(result)

                if cmd == Exit
                then Breaks.break()

              catch
                // don't catch parse errors here without advancing the input stream!
                case result: Error =>
                  report.report(result, printSuccess)

                  if cmd != Done then
                    done.append(cmd)
                  results.append(result)

                  if (!incremental)
                    Breaks.break()

    catch
      // catches parse errors, which have no command
      case result: Error =>
        report.report(result, printSuccess)
        results.append(result)

    (done.toList, results.toList)
