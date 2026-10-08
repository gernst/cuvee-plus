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

      // the example `file` as a test of the command line in its first line (see test.Expected)
      case Array("-test", file) =>
        System.out.flush()
        sys.exit(cuvee.test.Expected.main(file))

      case _ =>
        val (code, _, _) = pipe(args.toList)
        System.out.flush()
        sys.exit(code)

  def run(args: String*): (List[Cmd], List[Result]) =
    run(args.toList)

  def run(args: List[String], sinks: List[Sink] = Nil): (List[Cmd], List[Result]) =
    val (_, cmds, results) = pipe(args, sinks)
    (cmds, results)

  def pipe(args: List[String], sinks: List[Sink]): (Int, List[Cmd], List[Result]) =
    pipe(Config.parse(Config.default, args), sinks)

  def pipe(args: List[String]): (Int, List[Cmd], List[Result]) =
    pipe(args, Nil)

  // the output is additionally passed to `sinks`, e.g. to collect the commands in tests,
  // returns the exit code, the processed commands, and the results (see Pipe.run)
  def pipe(config: Config, sinks: List[Sink]): (Int, List[Cmd], List[Result]) =
    Debug.modules = config.debug

    // fresh names are deterministic per run
    Var.reset()
    Param.reset()

    val reader = config.reader
    val (init, cmds) = config.input.source(config, reader)

    // the declarations that the receiver knows are dropped before it, e.g. the prelude of the language of the output
    // for a printer, before further sinks, e.g. of tests, which therefore see what the receiver sees;
    // the reports are in the language of the input
    val main = config.sink(config, config.output.printer, init)
    val sink = Sink.filter(main.knows, Sink.tee(main, sinks*))
    val report = config.report(config, config.input.printer)
    val stages = config.stages(init, sink)

    // stages flush pending declarations only on control commands and queries,
    // therefore the end of the input is marked by Done
    val cmds_ = cmds #::: LazyList(Done)

    Pipe.run(cmds_, stages, report, incremental = false)
