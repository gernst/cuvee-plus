package cuvee

import java.io.PrintStream
import java.io.InputStreamReader
import java.io.FileReader

import util.Name

import cuvee.core._
import cuvee.pipe._
import cuvee.smtlib.Solver
import cuvee.simplify.Fuse
import cuvee.simplify.Simplify
import cuvee.prove.Prove
import cuvee.transform.Fallback
import cuvee.transform.Flat
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

  // the language of the logic is SMT-LIB, whose output drops the prelude
  val svlib =
    Lang("SV-LIB", cuvee.svlib.Source, cuvee.svlib.Printer, Set("smt2", "svlib"))

  // its output is the language of the input file of the task (see Config.parse and yml.Source)
  val yml =
    Lang("SV-COMP task definition", cuvee.yml.Source, cuvee.c.Printer, Set("c"), false)

// input, output: the languages of the input file, whose printer prints the reports, and of the output,
// the output does not contain the declarations of its features (see Sink.known and Cuvee.pipe)
case class Config(
    file: Option[String],
    input: Lang,
    output: Lang,
    // built from the final configuration, such that the order of the command line options does not matter,
    // the sink of the output without solver or with -print null
    sink: (Config, Printer, State) => Sink,
    report: (Config, Printer) => Report,
    // the solver of -z3 or -cvc5, given the timeout, which receives the output, see receiver
    solver: Option[Int => Solver] = None,
    // -verify: the answers correct, incorrect, or unknown (see pipe.Verify)
    verify: Boolean = false,
    // -witness: the file of the witness of SV-COMP for the answer of -verify to a C program (see yml.Witness)
    witness: Option[String] = None,
    transforms: List[Transform] = Nil,
    // per query, in milliseconds
    timeout: Int = 1000,
    // the data model of C for 32 or 64 bit Linux, ILP32 or LP64, i.e., the sizes of the integer types
    arch: Int = 64,
    // whether the nondeterministic values of C input range over all integers, instead of the values of their types,
    // except that unsigned ones are nonnegative (see c.Parser.havoc)
    unbounded: Boolean = false,
    // -entry: the procedure where executions start, by default main in C (see entryPoint)
    entry: Option[String] = None,
    // the features added to the languages of the input and of the output, e.g. teq by -teq, kept for -print;
    // teq injects the modules of the lemma database (see injected)
    known: Set[String] = Set(),
    // the further modules of the lemma database, e.g. by -include teq:aggregation, with the sources that parse them
    modules: List[(Source, String)] = Nil,
    // the files of the user that are injected into the input after the modules, with the sources of their
    // languages (see -include and Source.apply)
    includes: List[(Source, String)] = Nil,
    // the lines of stdout and stderr, which tests capture instead (see test.Expected)
    stdout: PrintStream = System.out,
    stderr: PrintStream = System.err,
    // whether -simplify reports the rules that it applies to each assertion (see Simplify.apply)
    rules: Boolean = false,
    // keep last
    debug: Set[String] = Set()
):
  def using(transform: Transform) =
    copy(transforms = transforms :+ transform)

  // the configuration with `feature` known to the languages of the input and of the output
  def having(feature: String) =
    copy(input = input.having(feature), output = output.having(feature), known = known + feature)

  // the configuration that injects the file `file` of the user into the input, parsed by `source`
  def including(source: Source, file: String) =
    copy(includes = includes :+ (source, file))

  // the source of the program, that of the input file of a task definition for one
  def program: Source =
    if input.source == cuvee.yml.Source then cuvee.yml.Source.lang(file).source else input.source

  // the procedure where executions start, -entry or main in C, as SV-COMP has it; none otherwise, where the
  // transforms that need one say so (Horn), SV-LIB starts at its verify-call commands instead; which procedures
  // are checked is up to the technique: VCGen checks all against their contracts, TEQ inlines the others
  def entryPoint: Option[Name] =
    entry.map(Name(_, None)).orElse(if program == cuvee.c.Source then Some(Name("main", None)) else None)

  // the modules of the lemma database that are injected into the input after its prelude (see Source.apply):
  // teq.dfy of -teq (see TEQ.modules) if the feature teq is known, then the further ones, each once, such that the
  // order of the options does not matter
  def injected =
    val modules_ = if known.contains("teq") then TEQ.modules.map((cuvee.dafny.Source, _)) else Nil
    (modules_ ++ modules).distinct

  // the receiver of the output, by the final configuration: the answers with -verify, with or without a solver,
  // otherwise the solver, if there is one, which checks the output, otherwise the sink of the output, e.g. a printer
  def receiver(init: State): Sink =
    if verify then
      val answers = cuvee.pipe.Verify.sink(solver.map(_(timeout)), stderr)
      witness.map(cuvee.yml.Witness.sink(this, _, answers)).getOrElse(answers)
    else solver.map(solver => Solver.sink(solver(timeout), init, stderr)).getOrElse(sink(this, output.printer, init))

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
  val default =
    Config(None, Lang.smtlib, Lang.smtlib, (config, printer, _) => Sink.stream(config.stdout, printer, config.output.features), (config, printer) => Report.stream(config.stderr, printer))

  def flag(key: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(None, help, action)

  def flag(key: String, args: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(Some(args), help, action)

  val debug_ =
    flag("-debug", "<modules>", "print the steps of the comma-separated <modules>: simplify, rewrite, match, conditions, forward, and views (of -simplify and -prove, see doc/prove.md), solver (the communication with the solvers)"):
      case (config, arg :: rest) =>
        val modules = arg.split(",")
        val config_ = config.copy(debug = config.debug ++ modules)
        (config_, rest)

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
    flag("-rules", "report the rewrite rules that -simplify and -prove apply to each assertion, by their names, as (set-info :used ((name count) ...)) after it"):
      case (config, rest) =>
        val config_ = config.copy(rules = true)
        (config_, rest)

  val simplify =
    flag("-simplify", "contextual simplification of formulas and function definitions, with the rewrite rules of lemmas and axioms with :rw"):
      case (config, rest) =>
        val config_ = config.using(Simplify)
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
        (config.copy(entry = Some(name)), rest)

  val unbounded =
    flag("-unbounded", "nondeterministic values of C input are unbounded integers, unsigned ones nonnegative, instead of within the ranges of their types"):
      case (config, rest) =>
        val config_ = config.copy(unbounded = true)
        (config_, rest)

  // the solvers receive the output, which they check, i.e., goals and lemmas must hold, or verify (-verify)
  val z3 =
    flag("-z3", "pass the output to z3, which checks it: goals and lemmas must hold, assertions and check-sat are passed through, the answers to queries are reported; lemmas with :free are assumed"):
      case (config, rest) =>
        val config_ = config.copy(solver = Some(Solver.z3))
        (config_, rest)

  val cvc5 =
    flag("-cvc5", "pass the output to cvc5, which checks it, as with -z3"):
      case (config, rest) =>
        val config_ = config.copy(solver = Some(Solver.cvc5))
        (config_, rest)

  // the answers are reported on stdout, the output is not printed
  val verify =
    flag("-verify", "instead of the output, answer correct, incorrect, or unknown to each verify-call, or once to the input without verify-call: whether the program satisfies its specification, with the solver if there is one; a refutation is incorrect unless the goal is :abstract or applies a function declared :abstract"):
      case (config, rest) =>
        val config_ = config.copy(verify = true, report = (config, printer) => Report.stream(config.stdout, printer))
        (config_, rest)

  // implies -verify, whose answer the witness is for
  val witness =
    flag("-witness", "<file>", "answer as -verify, and write the witness of SV-COMP (format 2.0) for the answer to a C program to <file>: for correct an invariant set without invariants, for incorrect a violation sequence whose target is the call of reach_error, if there is exactly one; nothing for unknown"):
      case (config, name :: rest) =>
        verify._2.action((config.copy(witness = Some(name)), rest))

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
      "print the output in <lang> instead of the language of the input: smt2, svlib, dfy, bpl, c (named by their file extensions), lean (the logic only), scala (the internal representation), or null (nothing)"
    ):
      case (config, name :: rest) if langs.contains(name) =>
        val config_ = config.printing(langs(name))
        (config_, rest)

      case (config, "lean" :: rest) =>
        val config_ = config.printing(Lang.lean)
        (config_, rest)

      // the declarations that the output drops remain those of the language of the output so far
      case (config, "null" :: rest) =>
        val config_ = config.copy(output = config.output.copy(printer = Printer.silent))
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
  // teq:<concept> is the module <concept>.dfy of the lemma database (resources/cuvee/teq), e.g. teq:sorted, which
  // the output hides like the rest of the database if the feature teq is known (-teq), and prints otherwise, e.g.
  // for -print lean of the database
  val include =
    flag("-include", "<file>", "inject <file> into the input after its prelude, parsed in the language of its extension; teq:<concept> injects the module <concept> of the lemma database of -teq: aggregation, arithmetic, arrays, counters, search, sorted, strides, unsigned"):
      // a module that does not exist is reported by its name, e.g. teq:sorting, renamed to teq:sorted on Oct 13, 2026
      case (config, file :: rest) if file.startsWith("teq:") =>
        val module = TEQ.module(file.drop(4))
        if getClass.getResource(module) == null
        then Error.raise("unknown module of the lemma database (resources/cuvee/teq)", file)
        (config.copy(modules = config.modules :+ (cuvee.dafny.Source, module)), rest)
      case (config, file :: rest) if langs.get(file.suffix).exists(_ != Lang.yml) =>
        (config.including(langs(file.suffix).source, file), rest)

  // the options in groups, in the order of doc/options.md, for -help
  val groups = List(
    "input" -> List(arch, unbounded, entry_, include, hybrid),
    "transformations" -> List(vcgen, teq, chc, flat, simplify, prove, rules, fallback, split, monomorph, fuse),
    "output" -> List(print_, linewidth, known_, output),
    "solvers and answers" -> List(z3, cvc5, timeout_, verify, witness),
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
    println("    run the example <file> with the command line of its first line and compare with name.out and name.err; with a .csv file, check a database of expected results")
    println("  -record <files>")
    println("    print the rows of a database of expected results for <files>")
    println("  -help")
    println("    list the options")
    println("  -version")
    println("    print the version")

  // the version, also of the producer of witnesses (see yml.Witness)
  val release = "0.46.20"

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
        arguments(config_, rest)

      case _ =>
        Error.raise("unsupported command line option or input file", args)
