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

      // on a thread with a large stack for deeply nested input, e.g. the hundreds of nested conditionals in the
      // outputs of the reducers of SV-COMP, which the parsers and transforms recurse into;
      // an uncaught exception is reported by the thread, and the exit code stays 1
      case _ =>
        // -svcomp as the first argument stands for the options of SV-COMP, the other arguments follow them
        val args_ =
          if args.headOption == Some("-svcomp")
          then svcomp ++ args.tail
          else args.toList
        var code = 1
        val thread = Thread(null, () => code = pipe(args_)._1, "cuvee", 1L << 30)
        thread.start()
        thread.join()
        System.out.flush()
        sys.exit(code)

  def run(args: String*): (List[Cmd], List[Error]) =
    run(args.toList)

  def run(args: List[String], sinks: List[Sink] = Nil): (List[Cmd], List[Error]) =
    val (_, cmds, errors) = pipe(args, sinks)
    (cmds, errors)

  // the options of the participation in SV-COMP, which -svcomp stands for, such that the entry of fm-tools and the
  // benchmark definitions can pass -svcomp and a new version of Cuvée change them without a change there: trace
  // equation systems with the modules of the lemma database (series after aggregation and arithmetic, whose sum and pow
  // it uses), the deduction engine with two rounds of splitting, and the witness of the answer; the fallback to z3
  // for the goals that remain is passed after it (-fallback -z3 -timeout <ms>)
  val svcomp = List(
    "-teq",
    "-include", "teq:aggregation",
    "-include", "teq:arithmetic",
    "-include", "teq:arrays",
    "-include", "teq:counters",
    "-include", "teq:search",
    "-include", "teq:sorted",
    "-include", "teq:strides",
    "-include", "teq:unsigned",
    "-include", "teq:series",
    "-prove", "-split", "-prove", "-split", "-prove",
    "-witness", "witness.yml"
  )

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
    val report = config.reporter
    val stages = config.stages(init, sink)

    // stages flush pending declarations only on control commands and queries,
    // therefore the end of the input is marked by Done
    val cmds_ = cmds #::: LazyList(Done)

    Pipe.run(cmds_, stages, report, incremental = false)
