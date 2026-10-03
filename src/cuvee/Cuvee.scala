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

  def run(args: List[String]) =
    val config = Config.parse(Config.default, args)
    Debug.modules = config.debug

    val reader = config.reader
    val (init, cmds) = config.source(reader)

    val printer = config.printer
    val sink = config.sink(init, printer)
    val report = config.report(printer)
    val stages = config.stages(init, sink)

    // stages flush pending declarations only on control commands and queries,
    // therefore the end of the input implies exit
    val cmds_ = cmds #::: LazyList(Exit)

    Pipe.run(cmds_, stages, report, incremental = false)
