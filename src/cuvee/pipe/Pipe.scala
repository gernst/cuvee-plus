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
// returns the exit code of the run (see Cuvee.main), 0 if it was not stopped or only by an error of an incremental
// run, the commands that were processed, and the errors, whereas the other results are only reported (see
// Report.collect)
object Pipe:
  val ExternalError = 1
  val InternalError = 2

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
    val errors = mutable.ListBuffer[Error]()

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
                val (result, added, next) = sink.query(cmd)
                sink = next

                // the answers to queries added by a transform are reported only if the command has no answer,
                // e.g. Done, which is not part of the input, and whose own answer is never reported
                val answers =
                  if result == Ack.Done && added.nonEmpty then added
                  else if cmd == Done && result == Ack.Done then Nil
                  else List(result)

                if answers.nonEmpty then
                  for result <- answers
                  do report.report(result, printSuccess)
                  if cmd != Done then done.append(cmd)

                if cmd == Exit
                then Breaks.break()

              catch
                // don't catch parse errors here without advancing the input stream!
                case result: Error =>
                  report.report(result, printSuccess)

                  if cmd != Done then
                    done.append(cmd)
                  errors.append(result)

                  if (!incremental)
                    code = ExternalError
                    Breaks.break()

                case NonFatal(cause) =>
                  val result = internal(cause)
                  report.report(result, printSuccess)

                  if cmd != Done then
                    done.append(cmd)
                  errors.append(result)
                  code = InternalError
                  Breaks.break()

    catch
      // catches parse errors, which have no command
      case result: Error =>
        report.report(result, printSuccess)
        errors.append(result)
        if !incremental then code = ExternalError

      case NonFatal(cause) =>
        val result = internal(cause)
        report.report(result, printSuccess)
        errors.append(result)
        code = InternalError

    (code, done.toList, errors.toList)
