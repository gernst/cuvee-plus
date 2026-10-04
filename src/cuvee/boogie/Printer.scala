package cuvee.boogie

import cuvee.core._

// placeholder until the Boogie printer is implemented: prints SMT-LIB
object Printer extends cuvee.pipe.Printer:
  def lines(res: Result) = cuvee.smtlib.Printer.lines(res)
  def lines(cmd: Cmd) = cuvee.smtlib.Printer.lines(cmd)
  def lines(typ: Type) = cuvee.smtlib.Printer.lines(typ)
  def lines(expr: Expr) = cuvee.smtlib.Printer.lines(expr)
  def lines(prog: Prog) = cuvee.smtlib.Printer.lines(prog)
