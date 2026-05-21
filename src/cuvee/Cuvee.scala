package cuvee

import cuvee.core._
import java.io.InputStreamReader

case class Name(name: String, index: Option[Int])

object Name:
  given Conversion[String, Name] =
    (name: String) => Name(name, None)

@main
def run() =
  import cuvee.pipe._

  val scanner = sexpr.Scanner(new InputStreamReader(System.in))
  val grammar = sexpr.Grammar
  val source = Source.read(scanner, grammar)

  val printer = Printer.default
  val sink = Sink.stdout(printer)

  val report = Report.stderr(printer)

  Pipe.run(source, sink, report, true)
