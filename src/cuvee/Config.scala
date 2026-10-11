package cuvee

import java.io.PrintStream
import java.io.InputStreamReader
import java.io.FileReader

import cuvee.core._
import cuvee.pipe._
import cuvee.smtlib.Solver
import cuvee.simplify.Fuse
import cuvee.simplify.Simplify
import cuvee.transform.Fallback
import cuvee.transform.Flat
import cuvee.transform.Monomorph
import cuvee.transform.Split
import cuvee.verify.Horn
import cuvee.verify.TEQ
import cuvee.verify.Verify

case class Flag(
    args: Option[String],
    help: String,
    action: PartialFunction[(Config, List[String]), (Config, List[String])]
)

// a language with the source that reads it and the printer that writes it,
// features: the features that it has built in, whose declarations are not printed (see Sink.known),
// beyond its file extension e.g. hybrid for the definitions of parallel composition in Dafny
// (resources/cuvee/dafny/hybrid.dfy, see -hybrid) and teq for trace equation systems (resources/cuvee/teq.dfy, see -teq),
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
  // declarations with the attribute {:lean}, e.g. the datatypes Nat and List of teq.dfy
  val lean =
    Lang("Lean", cuvee.smtlib.Source, cuvee.lean.Printer, Set("smt2", "dfy", "bpl", "c", "lean"))

  // its output is C (see Config.parse)
  val yml =
    Lang("SV-COMP task definition", cuvee.yml.Source, cuvee.c.Printer, Set("c"), false)

// input, output: the languages of the input file, whose printer prints the reports, and of the output,
// the output does not contain the declarations of its features (see Sink.known and Cuvee.pipe)
case class Config(
    file: Option[String],
    input: Lang,
    output: Lang,
    // built from the final configuration, such that the order of the command line options does not matter
    sink: (Config, Printer, State) => Sink,
    report: (Config, Printer) => Report,
    transforms: List[Transform] = Nil,
    // per query, in milliseconds
    timeout: Int = 1000,
    // the data model of C for 32 or 64 bit Linux, ILP32 or LP64, i.e., the sizes of the integer types
    arch: Int = 64,
    // whether the nondeterministic values of C input range over all integers, instead of the values of their types,
    // except that unsigned ones are nonnegative (see c.Parser.havoc)
    unbounded: Boolean = false,
    // the features added to the languages of the input and of the output, e.g. teq by -teq, kept for -print
    known: Set[String] = Set(),
    // the files of features that are injected into the input after its prelude, with the sources that parse them,
    // e.g. teq.dfy by -teq (see Source.apply)
    features: List[(Source, String)] = Nil,
    // the files of the user that are injected into the input after the files of features, with the sources of their
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

  // the configuration that injects `file` into the input, parsed by `source`
  def injecting(source: Source, file: String) =
    copy(features = features :+ (source, file))

  // the configuration that injects the file `file` of the user into the input, parsed by `source`
  def including(source: Source, file: String) =
    copy(includes = includes :+ (source, file))

  // the configuration that knows the feature teq and injects the modules of its lemma database (see TEQ.modules),
  // in their order
  def injectingTEQ =
    TEQ.modules.foldLeft(having("teq"))((config, module) => config.injecting(cuvee.dafny.Source, module))

  // whether the lemma database of -teq is injected already, e.g. by -known teq before -teq
  def injectsTEQ =
    features.exists(_._2 == TEQ.modules.head)

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
    flag("-debug", "<modules>", "enable debugging in <modules> (comma-separated list)"):
      case (config, arg :: rest) =>
        val modules = arg.split(",")
        val config_ = config.copy(debug = config.debug ++ modules)
        (config_, rest)

  val verify =
    flag("-verify", "generate verification conditions for procedures"):
      case (config, rest) =>
        val config_ = config.using(Verify)
        (config_, rest)

  val teq =
    flag("-teq", "generate verification conditions for procedures by symbolic execution and trace equation systems"):
      case (config, rest) =>
        val config_ = (if config.injectsTEQ then config.usingMath else config.usingMath.injectingTEQ).using(TEQ)
        (config_, rest)

  // Horn clauses are no C programs, they are printed in SMT-LIB instead (input files are parsed first, see parse)
  val chc =
    flag("-chc", "generate constrained Horn clauses for procedures"):
      case (config, rest) =>
        val config_ = config.usingMath.using(Horn)
        (config_, rest)

  val flat =
    flag("-flat", "replace arguments of predicates that are records by their fields, e.g. after -chc"):
      case (config, rest) =>
        val config_ = config.using(Flat)
        (config_, rest)

  val split =
    flag("-split", "split goals and lemmas into individual obligations, e.g. after -verify"):
      case (config, rest) =>
        val config_ = config.using(Split)
        (config_, rest)

  val monomorph =
    flag("-monomorph", "replace polymorphic functions by their monomorphic instances, e.g. before -z3"):
      case (config, rest) =>
        val config_ = config.using(Monomorph)
        (config_, rest)

  val fallback =
    flag("-fallback", "lower trace equation systems into first-order logic for solvers, e.g. after -teq -simplify"):
      case (config, rest) =>
        val config_ = config.using(Fallback)
        (config_, rest)

  val fuse =
    flag("-fuse", "fuse the compositions of defined functions in the requests fuse g(f(xs), ys) = ??? of Dafny input"):
      case (config, rest) =>
        val config_ = config.using(Fuse)
        (config_, rest)

  val rules =
    flag("-rules", "report the rewrite rules that -simplify applies to each assertion, by their names, as :used"):
      case (config, rest) =>
        val config_ = config.copy(rules = true)
        (config_, rest)

  val simplify =
    flag("-simplify", "simplify formulas and function definitions"):
      case (config, rest) =>
        val config_ = config.using(Simplify)
        (config_, rest)

  val hybrid =
    flag("-hybrid", "inject the definitions of parallel composition into Dafny input: chan, event, history, send, receive"):
      case (config, rest) =>
        val config_ = config.usingMath.having("hybrid")
        (config_, rest)

  val arch =
    flag("-arch", "<bits>", "the data model of C input, 32 or 64 bit Linux (ILP32 or LP64), e.g. for sizeof (default 64)"):
      case (config, (bits @ ("32" | "64")) :: rest) =>
        val config_ = config.copy(arch = bits.toInt)
        (config_, rest)

  val unbounded =
    flag("-unbounded", "nondeterministic values of C input are unbounded integers, unsigned ones nonnegative, instead of within the ranges of their types"):
      case (config, rest) =>
        val config_ = config.copy(unbounded = true)
        (config_, rest)

  val z3 =
    flag("-z3", "pass output to z3"):
      case (config, rest) =>
        val config_ = config.copy(sink = (config, _, init) => Solver.sink(Solver.z3(config.timeout), init))
        (config_, rest)

  val cvc5 =
    flag("-cvc5", "pass output to cvc5"):
      case (config, rest) =>
        val config_ = config.copy(sink = (config, _, init) => Solver.sink(Solver.cvc5(config.timeout), init))
        (config_, rest)

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
      "print the output in <lang> instead of the language of the input: smt2, dfy, bpl, c (named by their file extensions), lean (the logic only), scala (the internal representation), or null (nothing)"
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
  // teq also injects the declarations of teq.dfy into the input, as -teq does, but without its transform, e.g. for
  // the lemmas of a program over Nat and Trace
  val known_ =
    flag("-known", "<features>", "omit the declarations with the comma-separated attributes <features> from the output, e.g. dfy,teq, where teq also declares those of -teq in the input"):
      case (config, names :: rest) =>
        val features = names.split(",").map(_.trim).filter(_.nonEmpty).toSet
        val config_ = config.copy(output = config.output.copy(features = config.output.features ++ features), known = config.known ++ features)
        val config__ = if features.contains("teq") && !config_.injectsTEQ then config_.injectingTEQ else config_
        (config__, rest)

  // a file of the user, e.g. with lemmas, in the language of its extension; task definitions describe no declarations
  // teq:<concept> is the module <concept>.dfy of the lemma database (resources/cuvee/teq), e.g. teq:sorting, which
  // the output hides like the rest of the database if the feature teq is known (-teq), and prints otherwise, e.g.
  // for -print lean of the database
  val include =
    flag("-include", "<file>", "inject <file> into the input after its prelude, parsed in the language of its extension; teq:<concept> injects the module <concept> of the lemma database of -teq"):
      case (config, file :: rest) if file.startsWith("teq:") =>
        (config.injecting(cuvee.dafny.Source, TEQ.module(file.drop(4))), rest)
      case (config, file :: rest) if langs.get(file.suffix).exists(_ != Lang.yml) =>
        (config.including(langs(file.suffix).source, file), rest)

  val flags = Map(
    debug_,
    verify,
    teq,
    chc,
    flat,
    split,
    monomorph,
    fallback,
    fuse,
    simplify,
    rules,
    hybrid,
    arch,
    unbounded,
    z3,
    cvc5,
    timeout_,
    linewidth,
    output,
    print_,
    known_,
    include
  )

  // the languages by their file extensions
  val langs = Map(
    "smt2" -> Lang.smtlib,
    "dfy" -> Lang.dafny,
    "bpl" -> Lang.boogie,
    "c" -> Lang.c,
    // preprocessed C, e.g. of SV-COMP tasks
    "i" -> Lang.c,
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

    println("supported input/output dialects")
    for (suffix, lang) <- langs
    do println("  " + lang.help + " (extension ." + suffix + ")")
    println()

    println("command line options")
    for (key, flag) <- flags
    do
      flag.args match
        case None =>
          println("  " + key)
        case Some(args) =>
          println("  " + key + " " + args)
      println("    " + flag.help)
      println()

  def version() =
    println("Cuvée 0.36.3")

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
        val output = if input == Lang.yml then Lang.c else input
        val config_ = config.copy(file = Some(file), input = input, output = output)
        arguments(config_, rest)

      case _ =>
        Error.raise("unsupported command line option or input file", args)
