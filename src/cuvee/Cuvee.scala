package cuvee

import cuvee.core._
import cuvee.pipe._

case class Name(name: String, index: Option[Int]):
  def withIndex(index: Int) =
    Name(name, Some(index))

object Name:
  given Conversion[String, Name] =
    (name: String) => Name(name, None)

object Cuvee extends util.Main:
  def main(args: Array[String]) =
    args match
      case Array("-h") | Array("-help") | Array("--help") =>
        Config.help()

      case Array("-v") | Array("-version") | Array("--version") =>
        Config.version()

      case _ =>
        run(args.toList)

  def run(args: String*): (List[Cmd], List[Result]) =
    run(args.toList)

  def run(args: List[String]) =
    val config = Config.parse(Config.default, args)

    val reader = config.reader
    val cmds = config.source(reader)

    val printer = config.printer
    val sink = config.sink(printer)
    val report = config.report(printer)

    Pipe.run(cmds, sink, report, incremental = false)
