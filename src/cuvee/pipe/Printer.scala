package cuvee.pipe

import scala.annotation.targetName

import cuvee.core._

trait Printer:
  def lines(res: Result): List[String]
  def lines(cmd: Cmd): List[String]
  def lines(typ: Type): List[String]
  def lines(expr: Expr): List[String]
  def lines(prog: Prog): List[String]

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
