package cuvee.smtlib

import util.Tool

import cuvee.Debug

import cuvee.sexpr.Printer
import cuvee.pipe.Parser
import cuvee.core.Cmd

class Solver(cmd: String*):
  val (out, in, err, proc) = Tool.pipe(cmd*)

  val res: Iterator[String] = ???

  def destroy() =
    proc.destroy()

  def write(cmd: Cmd) =
    for (line <- Printer.lines(cmd))
    do
      Debug.info("solver", proc.pid + "> " + line)
      out.println(line)
    out.flush()

  def read() =
    val line = res.next()
    Debug.info("solver", proc.pid + "< " + line)
    line

  def ack(cmd: Cmd) =
    write(cmd)
    Parser.ack(read())
