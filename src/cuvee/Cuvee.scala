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

      // a database of expected results, e.g. benchmarks/sv-comp/dafny/expected.csv (see test.Database)
      case Array("-test", file) if file.endsWith(".csv") =>
        System.out.flush()
        sys.exit(cuvee.test.Database.test(file))

      case Array("-record", files*) =>
        System.out.flush()
        sys.exit(cuvee.test.Database.main(files.toList))

      // the example `file` as a test of the command line in its first line (see test.Expected)
      case Array("-test", file) =>
        System.out.flush()
        sys.exit(cuvee.test.Expected.main(file))

      // on a thread with a large stack for deeply nested input, e.g. the hundreds of nested conditionals in the
      // outputs of the reducers of SV-COMP, which the parsers and transforms recurse into;
      // an uncaught exception is reported by the thread, and the exit code stays 1
      case _ =>
        var code = 1
        val thread = Thread(null, () => code = pipe(args.toList)._1, "cuvee", 1L << 30)
        thread.start()
        thread.join()
        System.out.flush()
        sys.exit(code)

  def run(args: String*): (List[Cmd], List[Error]) =
    run(args.toList)

  def run(args: List[String], sinks: List[Sink] = Nil): (List[Cmd], List[Error]) =
    val (_, cmds, errors) = pipe(args, sinks)
    (cmds, errors)

  def pipe(args: List[String], sinks: List[Sink]): (Int, List[Cmd], List[Error]) =
    pipe(Config.parse(Config.default, args), sinks)

  def pipe(args: List[String]): (Int, List[Cmd], List[Error]) =
    pipe(args, Nil)

  // the output is additionally passed to `sinks`, e.g. to collect the commands in tests,
  // returns the exit code, the processed commands, and the errors (see Pipe.run)
  def pipe(config: Config, sinks: List[Sink]): (Int, List[Cmd], List[Error]) =
    Debug.modules = config.debug

    // fresh names are deterministic per run
    Var.reset()
    Param.reset()

    val reader = config.reader

    // the modules of the lemma database and the files of -include are parsed before the pipe runs, an error there,
    // e.g. a module that refers to declarations of another one that is not injected, is reported like a parse error
    val (init, cmds) =
      try config.input.source(config, reader)
      catch
        case result: Error =>
          config.report(config, config.input.printer).report(result, false)
          return (Pipe.ExternalError, Nil, List(result))

    // the declarations that the receiver knows are dropped before it, e.g. the prelude of the language of the output
    // for a printer, before further sinks, e.g. of tests, which therefore see what the receiver sees;
    // the reports are in the language of the input
    val main = config.receiver(init)
    val sink = Sink.filter(main.knows, Sink.tee(main, sinks*))
    val report = config.report(config, config.input.printer)
    val stages = config.stages(init, sink)

    // stages flush pending declarations only on control commands and queries,
    // therefore the end of the input is marked by Done
    val cmds_ = cmds #::: LazyList(Done)

    Pipe.run(cmds_, stages, report, incremental = false)
