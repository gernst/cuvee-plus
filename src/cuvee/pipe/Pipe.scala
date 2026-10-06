package cuvee.pipe

import scala.util.control.Breaks
import scala.util.control.NonFatal
import scala.collection.mutable

import cuvee.Debug
import cuvee.Error
import cuvee.core._
import cuvee.sexpr.Id

// runs the commands through the chain of sinks, reporting each result:
// print-success is handled here, since it concerns the reports, not the sinks;
// errors are reported and stop the run unless it is incremental, which continues with the next command;
// other exceptions are reported as internal errors and always stop the run;
// returns the exit code of the run (see Cuvee.main), the commands that were processed, and the results,
// 0 if it was not stopped or only by an error of an incremental run
object Pipe:
  val errorCode = 1
  val internalCode = 2

  // exceptions other than Error, whose stack trace is printed with -debug internal
  def internal(cause: Throwable): Error =
    if Debug.modules.contains("internal")
    then cause.printStackTrace()

    val result = Error("internal error", cause.getClass.getSimpleName, String.valueOf(cause.getMessage))
    result.initCause(cause)
    result

  def run(source: Iterable[Cmd], init: Sink, report: Report, incremental: Boolean) =
    var sink = init
    var printSuccess = false
    var code = 0

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

                // Done is not part of the input, its answer is reported only if it has one,
                // e.g. to a query added by a transform at the end of the input;
                // several answers to queries added by a transform are reported one by one
                if cmd != Done || result != Ack.Done then
                  for result <- Answers.flatten(result)
                  do
                    report.report(result, printSuccess)
                    results.append(result)
                  if cmd != Done then done.append(cmd)

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
                    code = errorCode
                    Breaks.break()

                case NonFatal(cause) =>
                  val result = internal(cause)
                  report.report(result, printSuccess)

                  if cmd != Done then
                    done.append(cmd)
                  results.append(result)
                  code = internalCode
                  Breaks.break()

    catch
      // catches parse errors, which have no command
      case result: Error =>
        report.report(result, printSuccess)
        results.append(result)
        if !incremental then code = errorCode

      case NonFatal(cause) =>
        val result = internal(cause)
        report.report(result, printSuccess)
        results.append(result)
        code = internalCode

    (code, done.toList, results.toList)
