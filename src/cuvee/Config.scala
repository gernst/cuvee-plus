package cuvee

import java.io.PrintStream
import java.io.InputStreamReader
import java.io.FileReader

import util.Name

import cuvee.core._
import cuvee.pipe._
import cuvee.smtlib.Solver
import cuvee.prove.Prove
import cuvee.transform.Fallback
import cuvee.transform.Flat
import cuvee.transform.Fuse
import cuvee.transform.Implement
import cuvee.transform.Monomorph
import cuvee.transform.Split
import cuvee.verify.Horn
import cuvee.verify.TEQ
import cuvee.verify.VCGen

case class Flag(
    args: Option[String],
    help: String,
    action: PartialFunction[(Config, List[String]), (Config, List[String])]
)

// a module of a feature, resources/cuvee/<feature>/<name>.dfy, injected by -include <feature>:<name>, with the
// source that parses it
case class Module(feature: String, source: Source, path: String)

// a feature whose modules -include injects (see Config.features): the modules that are injected before them if the
// feature is known or one of its modules is included, e.g. teq.dfy of -teq, and whether its modules need the feature
// to be known
case class Feature(entry: List[(Source, String)], needsKnown: Boolean)

// a language with the source that reads it and the printer that writes it,
// features: the features that it has built in, whose declarations are not printed (see Sink.known),
// beyond its file extension e.g. hybrid for the definitions of parallel composition in Dafny
// (resources/cuvee/dafny/hybrid.dfy, see -hybrid) and teq for trace equation systems (resources/cuvee/teq, see -teq),
// hasMath: whether it can express the output of transforms like -teq and -chc, otherwise the output is SMT-LIB
case class Lang(
    help: String,
    source: Source,
    printer: Printer,
    features: Set[String],
    hasMath: Boolean = true
):
  def having(feature: String) =
    copy(features = features + feature)

object Lang:
  val smtlib =
    Lang("SMT-LIB", cuvee.smtlib.Source, cuvee.smtlib.Printer, Set("smt2"))

  val dafny =
    Lang("Dafny", cuvee.dafny.Source, cuvee.dafny.Printer, Set("dfy"))

  val boogie =
    Lang("Boogie", cuvee.boogie.Source, cuvee.boogie.Printer, Set("bpl"))

  val c =
    Lang("C", cuvee.c.Source, cuvee.c.Printer, Set("c"), false)

  // output only (-print lean), there is no source of Lean, the one given is never used; Lean knows the built-in sorts
  // and functions of all languages, which its printer maps to their counterparts in Lean, or rejects, and the
  // declarations with the attribute {:lean}, e.g. the datatypes Nat and List of the lemma database (teq.dfy)
  val lean =
    Lang("Lean", cuvee.smtlib.Source, cuvee.lean.Printer, Set("smt2", "dfy", "bpl", "c", "lean"))

  // SV-LIB scripts are SMT-LIB scripts, read and written by the parser and printer of SMT-LIB, which know the
  // programs of SV-LIB (see smtlib.Parser.procedure), and start from its prelude; the language of the logic is
  // SMT-LIB, whose output drops the prelude
  val svlib =
    Lang("SV-LIB", cuvee.smtlib.Source, cuvee.smtlib.Printer, Set("smt2", "svlib"))

  // its output is the language of the input file of the task (see Config.parse and yml.Source)
  val yml =
    Lang("SV-COMP task definition", cuvee.yml.Source, cuvee.c.Printer, Set("c"), false)

// input, output: the languages of the input file and of the output, whose printer also prints the reports,
// the output does not contain the declarations of its features (see Sink.known and Cuvee.pipe)
case class Config(
    file: Option[String],
    input: Lang,
    output: Lang,
    // built from the final configuration, such that the order of the command line options does not matter,
    // the sink of the output without solver
    sink: (Config, Printer, State) => Sink,
    report: (Config, Printer) => Report,
    // the solver of -z3 or -cvc5, given the timeout, which receives the output, see receiver
    solver: Option[Int => Solver] = None,
    // -quiet: no output, only the reports, e.g. the answers
    quiet: Boolean = false,
    // -witness: the file of the witness of SV-COMP for the answers to a C program (see yml.Witness)
    witness: Option[String] = None,
    transforms: List[Transform] = Nil,
    // per query, in milliseconds
    timeout: Int = 1000,
    // -prove:steps: the bound on the rewrite steps of -prove per goal and per procedure, beyond which rewriting is
    // taken not to terminate (see Context.withRules)
    steps: Int = 1000,
    // the data model of C for 32 or 64 bit Linux, ILP32 or LP64, i.e., the sizes of the integer types
    arch: Int = 64,
    // whether the nondeterministic values of C input range over all integers, instead of the values of their types,
    // except that unsigned ones are nonnegative (see c.Parser.havoc)
    unbounded: Boolean = false,
    // -entry: the procedure where executions start, as SV-COMP has it main in C, set with the input file (see
    // arguments), none otherwise, where the transforms that need one say so (Horn), SV-LIB starts at its verify-call
    // commands instead; which procedures are checked is up to the technique: VCGen checks all against their
    // contracts, TEQ inlines the others
    entry: Option[Name] = None,
    // the features added to the languages of the input and of the output, e.g. teq by -teq, kept for -print;
    // teq injects the modules of the lemma database (see injected)
    known: Set[String] = Set(),
    // the modules of features, e.g. of the lemma database by -include teq:aggregation (see injected)
    modules: List[Module] = Nil,
    // the files of the user that are injected into the input after the modules, with the sources of their
    // languages (see -include and Source.apply)
    includes: List[(Source, String)] = Nil,
    // the lines of stdout and stderr, which tests capture instead (see test.Expected)
    stdout: PrintStream = System.out,
    stderr: PrintStream = System.err,
    // whether -prove reports the rules that it applies to each assertion (see Prove.used)
    rules: Boolean = false,
    // -instrument: -implement inlines the bodies of the implementations by methods instead of calling them
    instrument: Boolean = false,
    // -slice: the heads of loops in the simplification of procedures by -prove are their trace equation systems,
    // simplified and attached as invariants (see prove.Slice)
    slice: Boolean = false,
    // keep last
    debug: Set[String] = Set()
):
  def using(transform: Transform) =
    copy(transforms = transforms :+ transform)

  // the stage of the implementations once, for -implement and -instrument together
  def implementing =
    if transforms.contains(Implement) then this else using(Implement)

  // the configuration with `feature` known to the languages of the input and of the output
  def having(feature: String) =
    copy(input = input.having(feature), output = output.having(feature), known = known + feature)

  // the configuration that injects the file `file` of the user into the input, parsed by `source`
  def including(source: Source, file: String) =
    copy(includes = includes :+ (source, file))

  // the language of the program, that of the input file of a task definition for one; SMT-LIB and SV-LIB share
  // their source and printer, the file extension among the features tells them apart, e.g. svlib
  def program: Lang =
    if input.source == cuvee.yml.Source then cuvee.yml.Source.lang(file) else input

  // the modules that are injected into the input after its prelude (see Source.apply): the entries of the features
  // that are known or whose modules are included, e.g. teq.dfy of -teq (see TEQ.modules) and implement.dfy (see
  // Implement.modules), then the modules of -include <feature>:<name>, each once, such that the order of the options does
  // not matter, since the modules are written over the entries
  def injected: List[(Source, String)] =
    for Module(name, _, path) <- modules
    do
      Config.features.toMap.get(name) match
        case None =>
          Error.raise("unknown feature of -include <feature>:<name>", name)

        case Some(feature) =>
          Error.report(s"-include $name:<concept> needs -$name or -known $name", path):
            require(!feature.needsKnown || known.contains(name))

    val entries =
      for
        (name, feature) <- Config.features
        if known.contains(name) || modules.exists(_.feature == name)
        module <- feature.entry
      yield module

    val modules_ =
      for Module(_, source, path) <- modules
      yield (source, path)

    (entries ++ modules_).distinct

  // the receiver of the output, by the final configuration: the solver, if there is one, which answers the goals
  // and lemmas, otherwise the sink of the output, e.g. a printer, which answers them by their form
  def receiver(init: State): Sink =
    solver match
      case Some(solver) => Solver.sink(solver(timeout), init, stderr)
      case None         => sink(this, if quiet then Printer.silent else output.printer, init)

  // the reports of the run in the language of the output (-print), also to the witness with -witness,
  // and with -chc the answer to the check-sat of the clauses as the answer to the program (see Horn.report)
  def reporter: Report =
    val report_ = report(this, output.printer)
    val witnessed = witness.map(cuvee.yml.Witness.report(this, _, report_)).getOrElse(report_)
    if transforms.contains(Horn) then Horn.report(witnessed) else witnessed

  // the configuration with the output in `lang`, which knows the features added so far
  def printing(lang: Lang) =
    copy(output = lang.copy(features = lang.features ++ known))

  // the output in SMT-LIB if its language cannot express the output of a transform, e.g. C
  def usingMath =
    if output.hasMath then this else printing(Lang.smtlib)

  def reader =
    file match
      case None =>
        new InputStreamReader(System.in)

      case Some(file) =>
        new FileReader(file)

  // chain the transforms in order in front of `sink`,
  // all stages start from the same initial state `init` provided by the source
  def stages(init: State, sink: Sink): Sink =
    transforms.foldRight(sink):
      case (transform, next) =>
        Stage.empty(this, init, transform, next)

object Config:
  // the features whose modules -include <feature>:<name> injects, in the order of their entries: the lemma database
  // of -teq, and the implementations of -implement, which need nothing, since a translation keeps them
  val features = List(
    "teq" -> Feature(TEQ.modules, needsKnown = true),
    "implement" -> Feature(Implement.modules, needsKnown = false)
  )

  val default =
    Config(None, Lang.smtlib, Lang.smtlib, (config, printer, _) => Sink.stream(config.stdout, printer, config.output.features), (config, printer) => Report.stream(config.stderr, printer))

  def flag(key: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(None, help, action)

  def flag(key: String, args: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(Some(args), help, action)

  val debug_ =
    flag("-debug", "<modules>", "print the steps of the comma-separated <modules>: simplify, rewrite, match, conditions, forward, and views (of -prove, see doc/prove.md), solver (the communication with the solvers)"):
      case (config, arg :: rest) =>
        val modules = arg.split(",")
        val config_ = config.copy(debug = config.debug ++ modules)
        (config_, rest)

  // a transformation of the task, not a technique, hence a translation without it keeps the task as written
  val implement =
    flag("-implement", "replace the functions that functions and methods with {:implement pattern} implement, the pattern an application of the implemented function to a permutation of the inputs: an implementation by a function everywhere except in the implementations, one by a method, which may be nondeterministic, by calls in the expressions that programs execute, in the order of evaluation; applications of those in specifications are errors"):
      case (config, rest) =>
        (config.implementing, rest)

  val instrument =
    flag("-instrument", "-implement, where the applications of the functions implemented by methods with a body become those bodies instead of calls, e.g. for encodings that instrument the program; the inlined methods are dropped"):
      case (config, rest) =>
        (config.implementing.copy(instrument = true), rest)

  val vcgen =
    flag("-vcgen", "verification conditions for procedures by weakest preconditions: contracts, loops with invariants, termination measures, global variables, nondeterministic choice and iteration"):
      case (config, rest) =>
        val config_ = config.using(VCGen)
        (config_, rest)

  val teq =
    flag("-teq", "generate verification conditions for procedures by symbolic execution and trace equation systems, one trace per strongly connected component of the variables of a loop, with the lemma database teq.dfy"):
      case (config, rest) =>
        val config_ = config.usingMath.having("teq").using(TEQ)
        (config_, rest)

  // Horn clauses are no C programs, they are printed in SMT-LIB instead (input files are parsed first, see parse)
  val chc =
    flag("-chc", "constrained Horn clauses for procedures, for the inference of invariants, from the entry point"):
      case (config, rest) =>
        val config_ = config.usingMath.using(Horn)
        (config_, rest)

  val flat =
    flag("-flat", "replace arguments of predicates that are records by their fields, e.g. after -chc"):
      case (config, rest) =>
        val config_ = config.using(Flat)
        (config_, rest)

  val split =
    flag("-split", "split goals and lemmas into individual obligations forall xs. antecedents ==> conclusion, which the solvers report one by one"):
      case (config, rest) =>
        val config_ = config.using(Split)
        (config_, rest)

  val monomorph =
    flag("-monomorph", "replace polymorphic functions by their monomorphic instances, e.g. before -z3"):
      case (config, rest) =>
        val config_ = config.using(Monomorph)
        (config_, rest)

  val fallback =
    flag("-fallback", "lower the trace equation systems that remain into first-order logic for the solvers, e.g. after -teq -prove; the lowered goals are :abstract"):
      case (config, rest) =>
        val config_ = config.using(Fallback)
        (config_, rest)

  val fuse =
    flag("-fuse", "fuse the compositions of defined functions in the requests fuse g(f(xs), ys) = ??? of Dafny input"):
      case (config, rest) =>
        val config_ = config.using(Fuse)
        (config_, rest)

  val rules =
    flag("-rules", "report the rewrite rules that -prove applies to each assertion, by their names, as (set-info :used ((name count) ...)) after it"):
      case (config, rest) =>
        val config_ = config.copy(rules = true)
        (config_, rest)

  // the lemma database is injected as by -teq, whose transform does not run, such that procedures reach -prove
  val slice =
    flag("-slice", "simplify procedures with -prove, where the head of each loop is its trace equation system as by -teq, simplified and attached to the loop as an invariant; injects the lemma database teq.dfy, implies -prove"):
      case (config, rest) =>
        val config_ = config.usingMath.having("teq").copy(slice = true)
        (if config_.transforms.contains(Prove) then config_ else config_.using(Prove), rest)

  val steps_ =
    flag("-prove:steps", "<n>", "the bound on the rewrite steps of -prove per goal (default 1000), beyond which it reports that rewriting does not terminate"):
      case (config, n :: rest) if n.toIntOption.exists(_ > 0) =>
        val config_ = config.copy(steps = n.toInt)
        (config_, rest)

  val prove =
    flag("-prove", "prove the goals of -teq with the deduction engine of the package prove: congruence closure, a simplex, matching modulo the classes and the views of traces of several accumulators, forward lemmas (:fw)"):
      case (config, rest) =>
        val config_ = config.using(Prove)
        (config_, rest)

  val hybrid =
    flag("-hybrid", "inject the definitions of parallel composition into Dafny input: chan, event, history, send, receive"):
      case (config, rest) =>
        val config_ = config.usingMath.having("hybrid")
        (config_, rest)

  val arch =
    flag("-arch", "<bits>", "the data model of C input, 32 or 64 bit Linux (ILP32 or LP64), e.g. for sizeof; default 64, or the data model of an SV-COMP task"):
      case (config, (bits @ ("32" | "64")) :: rest) =>
        val config_ = config.copy(arch = bits.toInt)
        (config_, rest)

  val entry_ =
    flag("-entry", "<name>", "the procedure where executions start, which -teq and -chc check; default main in C, none otherwise (SV-LIB starts at its verify-call commands); -vcgen checks every procedure against its contract"):
      case (config, name :: rest) =>
        (config.copy(entry = Some(Name(name, None))), rest)

  val unbounded =
    flag("-unbounded", "nondeterministic values of C input are unbounded integers, unsigned ones nonnegative, instead of within the ranges of their types"):
      case (config, rest) =>
        val config_ = config.copy(unbounded = true)
        (config_, rest)

  // the solvers receive the output, which they check, i.e., they answer the goals and lemmas
  val z3 =
    flag("-z3", "pass the output to z3, which checks it: goals and lemmas are answered correct, incorrect, or unknown (unknown if the goal is :abstract or applies a function declared :abstract), assertions and check-sat are passed through, the answers to queries are reported; lemmas with :free are assumed"):
      case (config, rest) =>
        val config_ = config.copy(solver = Some(Solver.z3))
        (config_, rest)

  val cvc5 =
    flag("-cvc5", "pass the output to cvc5, which checks it, as with -z3"):
      case (config, rest) =>
        val config_ = config.copy(solver = Some(Solver.cvc5))
        (config_, rest)

  val witness =
    flag("-witness", "<file>", "write the witness of SV-COMP (format 2.0) for the verdict of the answers to a C program to <file>, incorrect if one is, correct if all are: for correct an invariant set without invariants, for incorrect a violation sequence whose target is the call of reach_error, if there is exactly one; nothing for unknown"):
      case (config, name :: rest) =>
        (config.copy(witness = Some(name)), rest)

  val timeout_ =
    flag("-timeout", "<ms>", "timeout per solver query in milliseconds (default 1000)"):
      case (config, ms :: rest) if ms.toIntOption.exists(_ > 0) =>
        val config_ = config.copy(timeout = ms.toInt)
        (config_, rest)

  val output =
    flag("-o", "<file>", "redirect output to <file> and report to stdout"):
      case (config, name :: rest) =>
        val config_ = config.copy(sink = (config, printer, _) => Sink.file(name, printer, config.output.features), report = (config, printer) => Report.stream(config.stdout, printer))
        (config_, rest)

  // a flag of its own rather than a printer, such that it does not depend on the order of -print
  val quiet =
    flag("-quiet", "print no output, only the reports, e.g. the answers to the goals and the errors"):
      case (config, rest) =>
        (config.copy(quiet = true), rest)

  // the printers are objects, all of which are set, such that the order of the options does not matter
  val linewidth =
    flag("-linewidth", "<n>", "lay out the output for lines of <n> characters (default 80)"):
      case (config, n :: rest) if n.toIntOption.exists(_ > 0) =>
        for lang <- langs.values.toList :+ Lang.lean
        do lang.printer.width = n.toInt
        cuvee.sexpr.Printer.width = n.toInt
        (config, rest)

  val print_ =
    flag(
      "-print",
      "<lang>",
      "print the output and the reports in <lang> instead of the language of the input: smt2, svlib, dfy, bpl, c (named by their file extensions), lean (the logic only), or scala (the internal representation)"
    ):
      case (config, name :: rest) if langs.contains(name) =>
        val config_ = config.printing(langs(name))
        (config_, rest)

      case (config, "lean" :: rest) =>
        val config_ = config.printing(Lang.lean)
        (config_, rest)

      case (config, "scala" :: rest) =>
        val config_ = config.copy(output = config.output.copy(printer = Printer.default))
        (config_, rest)

  // features that the receiver of the output knows, e.g. -known dfy,teq for a C program without the logic of the
  // preludes of Dafny and of -teq, whose declarations are dropped (see Sink.known), also after a later -print;
  // teq also injects the lemma database into the input, as -teq does, but without its transform, e.g. for
  // the lemmas of a program over Nat and Trace (see injected)
  val known_ =
    flag("-known", "<features>", "omit the declarations with the comma-separated attributes <features> from the output, e.g. dfy,teq, where teq also declares those of -teq in the input"):
      case (config, names :: rest) =>
        val features = names.split(",").map(_.trim).filter(_.nonEmpty).toSet
        val config_ = config.copy(output = config.output.copy(features = config.output.features ++ features), known = config.known ++ features)
        (config_, rest)

  // a file of the user, e.g. with lemmas, in the language of its extension; task definitions describe no declarations
  // <feature>:<name> is the module resources/cuvee/<feature>/<name>.dfy of a feature (see features), e.g. teq:sorted
  // of the lemma database, which the output hides like the rest of the database if the feature teq is known (-teq),
  // and prints otherwise, e.g. for -print lean of the database
  val include =
    flag("-include", "<file>", "inject <file> into the input after its prelude, parsed in the language of its extension; <feature>:<name> injects the module <name> of a feature: teq:<concept> of the lemma database of -teq (aggregation, arithmetic, arrays, counters, search, series, sorted, strides, unsigned), implement:<name> of the implementations of -implement"):
      // an unknown feature is reported with the input (see injected), a module that does not exist by the source
      // (see Source.resource)
      case (config, file :: rest) if file.contains(":") =>
        val (name, module) = file.splitAt(file.indexOf(":"))
        (config.copy(modules = config.modules :+ Module(name, cuvee.dafny.Source, s"/cuvee/$name/${module.drop(1)}.dfy")), rest)
      case (config, file :: rest) if langs.get(file.suffix).exists(_ != Lang.yml) =>
        (config.including(langs(file.suffix).source, file), rest)

  // the options in groups, in the order of doc/options.md, for -help
  val groups = List(
    "input" -> List(arch, unbounded, entry_, include, hybrid),
    "transformations" -> List(implement, instrument, vcgen, teq, chc, flat, prove, steps_, slice, rules, fallback, split, monomorph, fuse),
    "output" -> List(print_, quiet, linewidth, known_, output),
    "solvers and answers" -> List(z3, cvc5, timeout_, witness),
    "debugging" -> List(debug_)
  )

  val flags =
    groups.flatMap(_._2).toMap

  // the languages by their file extensions
  val langs = Map(
    "smt2" -> Lang.smtlib,
    "dfy" -> Lang.dafny,
    "bpl" -> Lang.boogie,
    "c" -> Lang.c,
    // preprocessed C, e.g. of SV-COMP tasks
    "i" -> Lang.c,
    "svlib" -> Lang.svlib,
    "yml" -> Lang.yml
  )

  extension (file: String)
    def suffix =
      val pos = file.lastIndexOf(".")
      if pos < 0
      then null
      else file.substring(pos + 1)

  def help() =
    version()
    copyright()
    println()

    println("usage: ./Cuvee.sh [options] file")
    println()

    // the languages in a fixed order, each with all of its extensions, e.g. C with .c and .i
    println("languages of the input, by the extension of the file")
    for lang <- List(Lang.smtlib, Lang.svlib, Lang.dafny, Lang.boogie, Lang.c, Lang.yml)
    do
      val suffixes = langs.toList.collect { case (suffix, `lang`) => "." + suffix }.sorted
      println("  " + lang.help + " (" + suffixes.mkString(", ") + ")")
    println()

    for (group, options) <- groups
    do
      println(group)
      for (key, flag) <- options
      do
        println("  " + key + flag.args.map(" " + _).getOrElse(""))
        println("    " + flag.help)
      println()

    // the commands of Cuvee.main, which take the whole command line
    println("other commands")
    println("  -test <file>")
    println("    run the example <file> with the command line of its first line and compare with name.out and name.err")
    println("  -svcomp ...")
    println("    as the first argument, the options of SV-COMP, followed by the other arguments: " + Cuvee.svcomp.mkString(" "))
    println("  -help")
    println("    list the options")
    println("  -version")
    println("    print the version")

  // the version, also of the producer of witnesses (see yml.Witness)
  val release = "0.53.8"

  def version() =
    println("Cuvée " + release)

  def copyright() =
    println("Gidon Ernst <gidon.ernst@gmail.com>")

  // the input files are parsed first, such that -print takes precedence regardless of its position
  def parse(config: Config, args: List[String]): Config =
    val (files, options) = split(args)
    arguments(config, files ++ options)

  // the input files among `args`, and the options with their argument, in order
  def split(args: List[String]): (List[String], List[String]) =
    args match
      case Nil =>
        (Nil, Nil)

      case flag :: arg :: rest if flags.get(flag).exists(_.args.isDefined) =>
        val (files, options) = split(rest)
        (files, flag :: arg :: options)

      case flag :: rest if flags.contains(flag) =>
        val (files, options) = split(rest)
        (files, flag :: options)

      case file :: rest =>
        val (files, options) = split(rest)
        (file :: files, options)

  // the output of an SV-COMP task is C, that of other inputs is in their language
  def arguments(config: Config, args: List[String]): Config =
    args match
      case Nil =>
        config

      case flag :: rest if flags.contains(flag) =>
        val action = flags(flag).action

        if action.isDefinedAt((config, rest))
        then
          val (config_, rest_) = action((config, rest))
          arguments(config_, rest_)
        else Error.raise("malformed argument for command line option", flag, rest)

      case file :: rest if langs.contains(file.suffix) =>
        val input = langs(file.suffix)
        val output = if input == Lang.yml then cuvee.yml.Source.lang(Some(file)) else input
        val config_ = config.copy(file = Some(file), input = input, output = output)
        // executions of C programs start in main, unless -entry says otherwise, before or after the file
        val entry = if config_.program.source == cuvee.c.Source then config.entry.orElse(Some(Name("main", None))) else config.entry
        arguments(config_.copy(entry = entry), rest)

      case _ =>
        Error.raise("unsupported command line option or input file", args)
