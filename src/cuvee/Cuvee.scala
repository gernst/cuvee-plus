package cuvee

import cuvee.core._
import cuvee.pipe._

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

  // the output is additionally passed to `sinks`, e.g. to collect the commands in tests
  def run(args: List[String], sinks: List[Sink] = Nil) =
    val config = Config.parse(Config.default, args)
    Debug.modules = config.debug

    val reader = config.reader
    val (init, cmds) = config.source(reader)

    val printer = config.printer
    val sink = Sink.tee(config.sink(init, printer), sinks*)
    val report = config.report(printer)
    val stages = config.stages(init, sink)

    // stages flush pending declarations only on control commands and queries,
    // therefore the end of the input is marked by Done
    val cmds_ = cmds #::: LazyList(Done)

    Pipe.run(cmds_, stages, report, incremental = false)
