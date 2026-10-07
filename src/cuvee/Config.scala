package cuvee

import java.io.InputStreamReader
import java.io.FileReader

import cuvee.core._
import cuvee.pipe._
import cuvee.smtlib.Solver
import cuvee.simplify.Simplify
import cuvee.transform.{Flat, Monomorph, Split}
import cuvee.verify.{Horn, TEQ, Verify}

case class Flag(
    args: Option[String],
    help: String,
    action: PartialFunction[(Config, List[String]), (Config, List[String])]
)

// a language with the source that reads it and the printer that writes it,
// features: the features that it has built in, whose declarations its printer drops (see Printer.filter),
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

  // its output is C (see Config.parse)
  val yml =
    Lang("SV-COMP task definition", cuvee.yml.Source, cuvee.c.Printer, Set("c"), false)

// input, output: the languages of the input file, whose printer prints the reports, and of the output,
// each of which drops the declarations of its features (see Printer.filter and Cuvee.pipe)
case class Config(
    file: Option[String],
    input: Lang,
    output: Lang,
    // built from the final configuration, such that the order of the command line options does not matter
    sink: (Config, Printer, State) => Sink,
    report: Printer => Report,
    transforms: List[Transform] = Nil,
    // per query, in milliseconds
    timeout: Int = 1000,
    // the data model of C for 32 or 64 bit Linux, ILP32 or LP64, i.e., the sizes of the integer types
    arch: Int = 64,
    // the features added to the languages of the input and of the output, e.g. teq by -teq, kept for -print
    features: Set[String] = Set(),
    // keep last
    debug: Set[String] = Set()
):
  def using(transform: Transform) =
    copy(transforms = transforms :+ transform)

  // the configuration with `feature` known to the languages of the input and of the output
  def having(feature: String) =
    copy(input = input.having(feature), output = output.having(feature), features = features + feature)

  // the configuration with the output in `lang`, which knows the features added so far
  def printing(lang: Lang) =
    copy(output = lang.copy(features = lang.features ++ features))

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
    Config(None, Lang.smtlib, Lang.smtlib, (_, printer, _) => Sink.stdout(printer), Report.stderr)

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
        val config_ = config.usingMath.having("teq").using(TEQ)
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
        val config_ = config.copy(sink = (_, printer, _) => Sink.file(name, printer), report = Report.stdout)
        (config_, rest)

  // the printers are objects, all of which are set, such that the order of the options does not matter
  val linewidth =
    flag("-linewidth", "<n>", "lay out the output for lines of <n> characters (default 80)"):
      case (config, n :: rest) if n.toIntOption.exists(_ > 0) =>
        for lang <- langs.values
        do lang.printer.width = n.toInt
        cuvee.sexpr.Printer.width = n.toInt
        (config, rest)

  val print_ =
    flag(
      "-print",
      "<lang>",
      "print the output in <lang> instead of the language of the input: smt2, dfy, bpl, c (named by their file extensions), scala (the internal representation), or null (nothing)"
    ):
      case (config, name :: rest) if langs.contains(name) =>
        val config_ = config.printing(langs(name))
        (config_, rest)

      // the declarations that the output drops remain those of the language of the output so far
      case (config, "null" :: rest) =>
        val config_ = config.copy(output = config.output.copy(printer = Printer.silent))
        (config_, rest)

      case (config, "scala" :: rest) =>
        val config_ = config.copy(output = config.output.copy(printer = Printer.default))
        (config_, rest)

  val flags = Map(
    debug_,
    verify,
    teq,
    chc,
    flat,
    split,
    monomorph,
    simplify,
    hybrid,
    arch,
    z3,
    cvc5,
    timeout_,
    linewidth,
    output,
    print_
  )

  // the languages by their file extensions
  val langs = Map(
    "smt2" -> Lang.smtlib,
    "dfy" -> Lang.dafny,
    "bpl" -> Lang.boogie,
    "c" -> Lang.c,
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
    println("Cuvée 0.27.2")

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
