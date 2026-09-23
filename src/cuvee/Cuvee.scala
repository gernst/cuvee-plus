package cuvee

import cuvee.core._
import cuvee.pipe._

case class Name(name: String, index: Option[Int]):
  def withIndex(index: Int) =
    Name(name, Some(index))

object Name:
  given Conversion[String, Name] =
    (name: String) => Name(name, None)

object foo extends util.Run(Cuvee, "examples/test.dafny")

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
