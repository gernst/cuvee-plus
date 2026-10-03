package cuvee.smtlib

import util.Tool

import cuvee.Debug
import cuvee.Error

import cuvee.core._
import cuvee.sexpr.Attrs
import cuvee.sexpr.Id

// an SMT solver as an external process, which is run with print-success
// so that each command is answered by exactly one line
class Solver(cmd: String*):
  val (out, in, err, proc) = Tool.pipe(cmd*)

  ack(SetOption("print-success", Id("true")))

  def destroy() =
    proc.destroy()

  def write(cmd: Cmd) =
    for (line <- Printer.lines(cmd))
    do
      Debug.info("solver", proc.pid + "> " + line)
      out.println(line)
    out.flush()

  def read() =
    val line = in.readLine()

    Error.report("solver terminated unexpectedly", cmd):
      require(line != null)

    Debug.info("solver", proc.pid + "< " + line)
    line

  def ack(cmd: Cmd): Ack =
    write(cmd)

    read() match
      case "success" =>
        Ack.Success

      case "unsupported" =>
        Ack.Unsupported

      case line =>
        Error.raise("solver error", cmd, line)

  def push(depth: Int = 1): Ack =
    ack(Push(depth))

  def pop(depth: Int = 1): Ack =
    ack(Pop(depth))

  def reset(): Ack =
    ack(Reset)

  def declare(fun: Fun): Ack =
    ack(DeclareFun(fun, Attrs.empty))

  def define(fun: Fun, body: Expr): Ack =
    ack(DefineFun(fun, body, Attrs.empty))

  def assert(phi: Expr): Ack =
    assert(Nil, phi)

  def assert(params: List[Param], phi: Expr): Ack =
    ack(Assert(Axiom, params, phi, Attrs.empty))

  // run f in a fresh scope that is popped afterwards, even if f fails
  def scoped[A](f: => A): A =
    push()
    try f
    finally pop()

  def check(): Status =
    write(CheckSat)

    read() match
      case "sat"     => Status.Sat
      case "unsat"   => Status.Unsat
      case "unknown" => Status.Unknown
      case line      => Error.raise("solver error", CheckSat, line)

  // phi is valid iff its negation is unsatisfiable, the assertion is retracted afterwards
  def valid(params: List[Param], phi: Expr): Status =
    scoped:
      assert(params, Not(phi))
      check()

object Solver:
  def z3() =
    new Solver("z3", "-in")

  def cvc5() =
    new Solver("cvc5", "--lang=smt2", "--incremental")

  // a sink that passes commands to the solver,
  // goals and lemmas are proved first and must be valid, lemmas are asserted subsequently
  class sink(solver: Solver) extends cuvee.pipe.Sink:
    def query(cmd: Cmd) =
      cmd match
        case Assert(Axiom, _, _, _) =>
          (solver.ack(cmd), this)

        case Assert(justify, params, phi, attrs) =>
          prove(justify, params, phi)

          if justify == Lemma
          then solver.ack(Assert(Axiom, params, phi, attrs))

          (Ack.Success, this)

        case CheckSat =>
          (solver.check(), this)

        // procedures are not understood by SMT solvers and must have been eliminated, e.g. with -verify
        case _: DeclareProc | _: DefineProc =>
          (Ack.Unsupported, this)

        case GetModel | Labels =>
          Error.raise("unsupported query", cmd)

        case Exit =>
          val ack = solver.ack(cmd)
          solver.destroy()
          (ack, this)

        case _ =>
          (solver.ack(cmd), this)

    def prove(justify: Justify, params: List[Param], phi: Expr) =
      solver.valid(params, phi) match
        case Status.Unsat =>

        case Status.Sat =>
          Error.raise(justify.toString.toLowerCase + " does not hold", Printer.lines(phi).mkString(" "))

        case Status.Unknown =>
          Error.raise(justify.toString.toLowerCase + " could not be proved", Printer.lines(phi).mkString(" "))
