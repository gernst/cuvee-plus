package cuvee.pipe

import scala.annotation.targetName

import cuvee.core._
import cuvee.simplify.Rule

trait Printer:
  // the width of the lines that the output is laid out for, set by -linewidth (see Config)
  var width = 80

  def lines(res: Result): List[String]
  def lines(cmd: Cmd): List[String]
  def lines(typ: Type): List[String]
  def lines(expr: Expr): List[String]
  def lines(prog: Prog): List[String]

  def lines(rule: Rule): List[String] =
    val Rule(params, vars, lhs, rhs, cond) = rule
    val cmd = Assert(Lemma, params.toList, All(vars.toList, Imp(cond, Eq(lhs, rhs))), Attrs.from("rw"))
    lines(cmd)

  @targetName("Printer.linesOfCmds")
  def lines(cmds: List[Cmd]): List[String] =
    for cmd <- cmds; line <- lines(cmd)
    yield line

  @targetName("Printer.linesOfTypes")
  def lines(types: List[Type]): List[String] =
    for typ <- types; line <- lines(typ)
    yield line

  @targetName("Printer.linesOfExprs")
  def lines(exprs: List[Expr]): List[String] =
    for expr <- exprs; line <- lines(expr)
    yield line

  @targetName("Printer.linesOfProgs")
  def lines(progs: List[Prog]): List[String] =
    for prog <- progs; line <- lines(prog)
    yield line

object Printer:
  def filter(features: Set[String], printer: Printer) =
    Filter(features, printer)

  // drops the top-level declarations that the receiver of the output knows by their features:
  // those of the preludes (resources/cuvee/*/prelude.*) name the languages that they are part of by attributes,
  // the file extensions smt2, dfy, bpl, and c, e.g. the tuples of Dafny are part of Dafny only,
  // and are therefore declared as datatypes in SMT-LIB,
  // and those injected with -teq and -hybrid are known to the input language (see Config.having)
  class Filter(features: Set[String], printer: Printer) extends Printer:
    def lines(res: Result) = printer.lines(res)
    def lines(typ: Type) = printer.lines(typ)
    def lines(expr: Expr) = printer.lines(expr)
    def lines(prog: Prog) = printer.lines(prog)

    def lines(cmd: Cmd) =
      cmd match
        case decl: Decl if features.exists(decl.attrs.contains) =>
          Nil

        case _ =>
          printer.lines(cmd)

  object default extends Printer:
    def lines(res: Result) = List(res.toString)
    def lines(cmd: Cmd) = List(cmd.toString)
    def lines(typ: Type) = List(typ.toString)
    def lines(expr: Expr) = List(expr.toString)
    def lines(prog: Prog) = List(prog.toString)

  object silent extends Printer:
    def lines(res: Result) = Nil
    def lines(cmd: Cmd) = Nil
    def lines(typ: Type) = Nil
    def lines(expr: Expr) = Nil
    def lines(prog: Prog) = Nil
