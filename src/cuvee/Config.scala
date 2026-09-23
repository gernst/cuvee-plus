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
    scanner: Reader => Scanner,
    grammar: Grammar,
    printer: Printer
)

object Lang:
  val smtlib =
    Lang("SMT-LIB", reader => new cuvee.sexpr.Scanner(reader), cuvee.sexpr.Grammar, cuvee.smtlib.Printer)

  val dafny =
    Lang("Dafny", reader => new cuvee.dafny.Scanner(reader), cuvee.dafny.Grammar, cuvee.smtlib.Printer)

case class Config(
    input: Option[String],
    scanner: Reader => Scanner,
    grammar: Grammar,
    printer: Printer,
    sink: (Printer => Sink),
    report: (Printer => Report),
    debug: Set[String]
) {
  def reader =
    input match
      case None =>
        new InputStreamReader(System.in)

      case Some(file) =>
        new FileReader(file)
}

object Config:
  val default =
    Config(None, reader => new cuvee.sexpr.Scanner(reader), cuvee.sexpr.Grammar, cuvee.smtlib.Printer, Sink.stdout, Report.stderr, Set())

  def flag(key: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(None, help, action)

  def flag(key: String, args: String, help: String)(action: PartialFunction[(Config, List[String]), (Config, List[String])]) =
    key -> Flag(Some(args), help, action)

  def lang(key: String, lang: Lang) =
    key -> lang

  val flags = Map(
    flag("-debug", "<modules>", "enable debugging in <modules> (comma-separated list)") { case (config, arg :: rest) =>
      val modules = arg.split(",")
      val config_ = config.copy(debug = config.debug ++ modules)
      (config_, rest)
    },

    flag("-o", "<file>", "redirect output to <file> and report to stdout") { case (config, name :: rest) =>
      val config_ = config.copy(sink = Sink.file(name), report = Report.stdout)
      (config_, rest)
    },

    flag("-print", "<format>", "override printer format") {
      case (config, name :: rest) if langs.contains(name) =>
        val lang = langs(name)
        val config_ = config.copy(printer = lang.printer)
        (config_, rest)

      case (config, "scala" :: rest) =>
        val config_ = config.copy(printer = Printer.default)
        (config_, rest)
    }
  )

  val langs = Map(
    lang(".smt2", Lang.smtlib),
    lang(".dfy", Lang.dafny)
  )

  extension (file: String)
    def suffix =
      val pos = file.lastIndexOf(".")
      if pos < 0
      then null
      else file.substring(pos)

  def help() =
    version()
    copyright()
    println()

    println("supported input/output dialects")
    for (suffix, lang) <- langs
    do println("  " + lang.help + " (" + suffix + ")")
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
    println("Cuvée 0.0.1")

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
        val Lang(help, scanner, grammar, printer) = langs(file.suffix)
        val config_ = config.copy(input = Some(file), scanner = scanner, grammar = grammar, printer = printer)
        parse(config_, rest)

      case _ =>
        Error.raise("unsupported command line option or input file", args)
