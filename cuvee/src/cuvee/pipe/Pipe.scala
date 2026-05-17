package cuvee.pipe

import scala.util.control.Breaks

import cuvee.Error
import cuvee.smtlib._

type Source = Iterable[Cmd]

type Transform = (List[Cmd], List[Cmd], State) => List[Cmd]

object Pipe:
  def run(source: Source, init: Sink, report: Report, incremental: Boolean) =
    var sink = init

    Breaks.breakable:
      for cmd <- source do
        try
          val (result, next) = sink.query(cmd)
          sink = next
          report.report(result)

        catch
          case Exit =>
            Breaks.break()

          case Error(msg) =>
            report.error(msg)

            if (!incremental)
              Breaks.break()
