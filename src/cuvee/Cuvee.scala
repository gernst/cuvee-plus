package cuvee

import cuvee.core._
import cuvee.pipe._

case class Name(name: String, index: Option[Int])

object Name:
  given Conversion[String, Name] =
    (name: String) => Name(name, None)

object Cuvee extends util.Main:
  def main(args: Array[String]) =
    import java.io.InputStreamReader

    val scanner = sexpr.Scanner(new InputStreamReader(System.in))
    val grammar = sexpr.Grammar
    val source = Source.read(scanner, grammar)

    val printer = Printer.default
    val sink = Sink.stdout(printer)

    val report = Report.stderr(printer)

    Pipe.run(source, sink, report, true)
