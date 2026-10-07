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
        val (code, _, _) = pipe(args.toList)
        System.out.flush()
        sys.exit(code)

  def run(args: String*): (List[Cmd], List[Result]) =
    run(args.toList)

  def run(args: List[String], sinks: List[Sink] = Nil): (List[Cmd], List[Result]) =
    val (_, cmds, results) = pipe(args, sinks)
    (cmds, results)

  // the output is additionally passed to `sinks`, e.g. to collect the commands in tests,
  // returns the exit code, the processed commands, and the results (see Pipe.run)
  def pipe(args: List[String], sinks: List[Sink] = Nil) =
    val config = Config.parse(Config.default, args)
    Debug.modules = config.debug

    // fresh names are deterministic per run
    Var.reset()
    Param.reset()

    val reader = config.reader
    val (init, cmds) = config.input.source(config, reader)

    val printer = config.output.printer
    // further sinks, e.g. of tests, receive the output like the sink of the configuration
    val sink = Sink.tee(config.sink(init, config), sinks.map(Sink.filter(config.output.builtin, _))*)
    val report = config.report(printer)
    val stages = config.stages(init, sink)

    // stages flush pending declarations only on control commands and queries,
    // therefore the end of the input is marked by Done
    val cmds_ = cmds #::: LazyList(Done)

    Pipe.run(cmds_, stages, report, incremental = false)
