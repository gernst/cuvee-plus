package cuvee

import cuvee.core._
import cuvee.pipe._

case class Name(name: String, index: Option[Int]):
  def withIndex(index: Int) =
    Name(name, Some(index))

object Name:
  given Conversion[String, Name] =
    (name: String) => Name(name, None)

object foo extends util.Run(Cuvee, "examples/test.dfy")

object Cuvee extends util.Main:
  def main(args: Array[String]) =
    val config = Config.parse(Config.default, args.toList)

    val reader = config.reader
    val scanner = config.scanner(reader)
    val source = Source.read(scanner, config.grammar)

    val printer = config.printer
    val sink = config.sink(printer)
    val report = config.report(printer)

    Pipe.run(source, sink, report, true)
