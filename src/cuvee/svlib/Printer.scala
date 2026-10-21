package cuvee.svlib

import cuvee.core._

// SV-LIB output: SMT-LIB, whose printer writes the programs of SV-LIB (see smtlib.Printer.lines(prog)), with an empty
// line after each command
object Printer extends cuvee.pipe.Printer:
  def lines(res: Result): List[String] =
    cuvee.smtlib.Printer.lines(res)

  def lines(typ: Type): List[String] =
    cuvee.smtlib.Printer.lines(typ)

  def lines(expr: Expr): List[String] =
    cuvee.smtlib.Printer.lines(expr)

  def lines(prog: Prog): List[String] =
    cuvee.smtlib.Printer.lines(prog)

  def lines(cmd: Cmd): List[String] =
    cuvee.smtlib.Printer.command(cmd) :+ ""
