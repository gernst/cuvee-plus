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
