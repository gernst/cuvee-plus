package cuvee

import java.io.IOException
import java.io.File
import java.io.Reader
import java.io.InputStreamReader
import java.io.FileReader

import scala.annotation.targetName

import cuvee.core._
import cuvee.pipe._

case class Flag(
    args: Option[String],
    help: String,
    action: PartialFunction[(Config, List[String]), (Config, List[String])]
)

case class Lang(
    help: String,
    source: Source,
    printer: Printer
)

object Lang:
  val smtlib =
    Lang("SMT-LIB", cuvee.smtlib.Source, cuvee.smtlib.Printer)

  val dafny =
    Lang("Dafny", cuvee.dafny.Source, cuvee.dafny.Printer)

  val boogie =
    Lang("Boogie", cuvee.boogie.Source, cuvee.boogie.Printer)

  val c =
    Lang("C", cuvee.c.Source, cuvee.c.Printer)

case class Config(
    input: Option[String],
    source: Source,
    printer: Printer,
    // built from the final configuration, such that the order of the command line options does not matter
    sink: (State, Config) => Sink,
    report: Printer => Report,
    transforms: List[Transform] = Nil,
    debug: Set[String] = Set(),
    overridePrinter: Boolean = false,
    // per query, in milliseconds
    timeout: Int = 1000,
    // the definitions of parallel composition in Dafny (resources/cuvee/dafny/hybrid.dfy)
    hybrid: Boolean = false,
    // the language of the printed output by its file extension, given with -print, the language of the input otherwise
    printed: Option[String] = None,
    // whether the output is passed to a solver, which reads SMT-LIB
    solver: Boolean = false
):
  // the language of the output by its file extension, whose declarations the output drops (see transform.Language)
  def language: String =
    if solver
    then "smt2"
    else printed.orElse(input.map(Config.suffix)).getOrElse("smt2")

  def reader =
    input match
      case None =>
        new InputStreamReader(System.in)

      case Some(file) =>
        new FileReader(file)

  // chain the transforms in order in front of `sink`, followed by the implicit last step that drops the declarations
  // that are part of the language of the output (see transform.Language),
  // all stages start from the same initial state `init` provided by the source
  def stages(init: State, sink: Sink): Sink =
    transforms.foldRight(cuvee.transform.Language.sink(language, sink): Sink):
      case (transform, next) =>
        Stage.empty(this, init, transform, next)

object Config:
  val default =
    Config(None, cuvee.smtlib.Source, cuvee.smtlib.Printer, (_, config) => Sink.stdout(config.printer), Report.stderr)

  def flag(key: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(None, help, action)

  def flag(key: String, args: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(Some(args), help, action)

  def lang(key: String, lang: Lang) =
    key -> lang

  val debug_ =
    flag("-debug", "<modules>", "enable debugging in <modules> (comma-separated list)"):
      case (config, arg :: rest) =>
        val modules = arg.split(",")
        val config_ = config.copy(debug = config.debug ++ modules)
        (config_, rest)

  val verify =
    flag("-verify", "generate verification conditions for procedures"):
      case (config, rest) =>
        val config_ = config.copy(transforms = config.transforms :+ cuvee.verify.Verify)
        (config_, rest)

  val teq =
    flag("-teq", "generate verification conditions for procedures by symbolic execution and trace equation systems"):
      case (config, rest) =>
        val config_ = config.copy(transforms = config.transforms :+ cuvee.verify.TEQ)
        (config_, rest)

  val chc =
    flag("-chc", "generate constrained Horn clauses for procedures"):
      case (config, rest) =>
        val config_ = config.copy(transforms = config.transforms :+ cuvee.verify.Horn)
        (config_, rest)

  val flat =
    flag("-flat", "replace arguments of predicates that are records by their fields, e.g. after -chc"):
      case (config, rest) =>
        val config_ = config.copy(transforms = config.transforms :+ cuvee.transform.Flat)
        (config_, rest)

  val split =
    flag("-split", "split goals and lemmas into individual obligations, e.g. after -verify"):
      case (config, rest) =>
        val config_ = config.copy(transforms = config.transforms :+ cuvee.transform.Split)
        (config_, rest)

  val monomorph =
    flag("-monomorph", "replace polymorphic functions by their monomorphic instances, e.g. before -z3"):
      case (config, rest) =>
        val config_ = config.copy(transforms = config.transforms :+ cuvee.transform.Monomorph)
        (config_, rest)

  val simplify =
    flag("-simplify", "simplify formulas and function definitions"):
      case (config, rest) =>
        val config_ = config.copy(transforms = config.transforms :+ cuvee.simplify.Simplify)
        (config_, rest)

  val hybrid =
    flag("-hybrid", "inject the definitions of parallel composition into Dafny input: chan, event, history, send, receive"):
      case (config, rest) =>
        val config_ = config.copy(hybrid = true)
        (config_, rest)

  val z3 =
    flag("-z3", "pass output to z3"):
      case (config, rest) =>
        val config_ = config.copy(sink = (init, config) => cuvee.smtlib.Solver.sink(cuvee.smtlib.Solver.z3(config.timeout), init, config.printer), solver = true)
        (config_, rest)

  val cvc5 =
    flag("-cvc5", "pass output to cvc5"):
      case (config, rest) =>
        val config_ = config.copy(sink = (init, config) => cuvee.smtlib.Solver.sink(cuvee.smtlib.Solver.cvc5(config.timeout), init, config.printer), solver = true)
        (config_, rest)

  val timeout_ =
    flag("-timeout", "<ms>", "timeout per solver query in milliseconds (default 1000)"):
      case (config, ms :: rest) if ms.toIntOption.exists(_ > 0) =>
        val config_ = config.copy(timeout = ms.toInt)
        (config_, rest)

  val output =
    flag("-o", "<file>", "redirect output to <file> and report to stdout"):
      case (config, name :: rest) =>
        val config_ = config.copy(sink = (_, config) => Sink.file(name)(config.printer), report = Report.stdout)
        (config_, rest)

  val print_ =
    flag("-print", "<lang>", "print the output in <lang> instead of the language of the input: smt2, dfy, bpl, c (named by their file extensions), scala (the internal representation), or null (nothing)"):
      case (config, name :: rest) if langs.contains(name) =>
        val lang = langs(name)
        val config_ = config.copy(printer = lang.printer, overridePrinter = true, printed = Some(name))
        (config_, rest)

      case (config, "null" :: rest) =>
        val config_ = config.copy(printer = Printer.silent, overridePrinter = true)
        (config_, rest)

      case (config, "scala" :: rest) =>
        val config_ = config.copy(printer = Printer.default, overridePrinter = true)
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
    z3,
    cvc5,
    timeout_,
    output,
    print_
  )

  val langs = Map(
    lang("smt2", Lang.smtlib),
    lang("dfy", Lang.dafny),
    lang("bpl", Lang.boogie),
    lang("c", Lang.c)
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
    println("Cuvée 0.18.11")

  def copyright() =
    println("Gidon Ernst <gidon.ernst@gmail.com>")

  def parse(config: Config, args: List[String]): Config =
    args match
      case Nil =>
        config

      case flag :: rest if flags.contains(flag) =>
        val action = flags(flag).action

        if action.isDefinedAt((config, rest))
        then
          val (config_, rest_) = action((config, rest))
          parse(config_, rest_)
        else Error.raise("malformed argument for command line option", flag, rest)

      case file :: rest if langs.contains(file.suffix) =>
        val Lang(help, source, printer) = langs(file.suffix)

        var config_ = config

        config_ = config_.copy(input = Some(file), source = source)

        if (!config_.overridePrinter)
        then config_ = config_.copy(printer = printer)

        parse(config_, rest)

      case _ =>
        Error.raise("unsupported command line option or input file", args)
