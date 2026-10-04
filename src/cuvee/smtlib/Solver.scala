package cuvee.smtlib

import util.Tool

import cuvee.Debug
import cuvee.Error

import cuvee.core._
import cuvee.sexpr.Attrs
import cuvee.sexpr.Grammar
import cuvee.sexpr.Id
import cuvee.sexpr.Str

// an SMT solver as an external process, which is run with print-success
// so that each command is answered by exactly one s-expression
class Solver(cmd: String*):
  val (out, in, err, proc) = Tool.pipe(cmd*)

  // responses may span several lines, e.g. models, and are read token by token
  var responses = new cuvee.sexpr.Scanner(in).input

  ack(SetOption("print-success", Id("true")))

  def destroy() =
    proc.destroy()

  def write(cmd: Cmd) =
    for (line <- Printer.lines(cmd))
    do
      Debug.info("solver", proc.pid + "> " + line)
      out.println(line)
    out.flush()

  // the response to `query` as an s-expression, errors reported by the solver are raised
  def read(query: Cmd): Any =
    Error.report("solver terminated unexpectedly", cmd, query):
      require(responses.nonEmpty)

    val (from, rest) =
      Error.report("invalid solver response", query):
        Grammar.sexpr.parse(responses)

    responses = rest
    Debug.info("solver", proc.pid + "< " + cuvee.sexpr.Printer.lines(from).mkString(" "))

    from match
      case List(Id("error"), Str(msg)) =>
        Error.raise("solver error", query, msg)

      case _ =>
        from

  def query(cmd: Cmd): Any =
    write(cmd)
    read(cmd)

  def ack(cmd: Cmd): Ack =
    Parser.ack(query(cmd))

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
    Parser.issat(query(CheckSat))

  // phi is valid iff its negation is unsatisfiable, the assertion is retracted afterwards
  def valid(params: List[Param], phi: Expr): Status =
    scoped:
      assert(params, Not(phi))
      check()

object Solver:
  // the timeout in milliseconds applies to each query, the solver keeps running afterwards
  def z3(timeout: Int = 1000) =
    new Solver("z3", "-in", "-t:" + timeout)

  // --strings-exp enables the extended functions on sequences, e.g. seq.nth
  def cvc5(timeout: Int = 1000) =
    new Solver("cvc5", "--lang=smt2", "--incremental", "--strings-exp", "--tlimit-per=" + timeout)

  // a sink that passes commands to the solver,
  // goals and lemmas are proved first and must be valid, lemmas are asserted subsequently,
  // the parser keeps track of the declarations known to the solver, starting from `init`,
  // and interprets the answers to queries in that state
  class sink(solver: Solver, init: State) extends cuvee.pipe.Sink:
    val parser = new Parser(init)

    def query(cmd: Cmd) =
      cmd match
        case Assert(Axiom, _, _, _) =>
          (solver.ack(cmd), this)

        // the solver's answer is reported if the goal is not valid, i.e., sat or unknown
        case Assert(justify, params, phi, attrs) =>
          val status = solver.valid(params, phi)
          if status != Status.Unsat then
            Error.raise(justify.toString.toLowerCase + " does not hold", status, Printer.lines(phi).mkString(" "))

          if justify == Lemma
          then solver.ack(Assert(Axiom, params, phi, attrs))

          (Ack.Success, this)

        case CheckSat =>
          (solver.check(), this)

        // procedures and global variables are not understood by SMT solvers and must have been eliminated, e.g. with -verify,
        // in particular, z3 accepts declare-var but does not acknowledge it with print-success
        case _: DeclareProc | _: DefineProc | _: DeclareVar =>
          (Ack.Unsupported, this)

        case _: GetInfo =>
          (Parser.info(solver.query(cmd)), this)

        case _: GetOption =>
          (Parser.value(solver.query(cmd)), this)

        case Labels =>
          (Parser.labels(solver.query(cmd)), this)

        case GetModel =>
          (parser.model(solver.query(cmd)), this)

        case Exit =>
          val ack = solver.ack(cmd)
          solver.destroy()
          (ack, this)

        case Done =>
          solver.destroy()
          (Ack.Done, this)

        // the state is updated only once the solver has accepted the declaration,
        // attributes are kept in the state but not sent to the solver
        case decl: Decl =>
          val state_ = parser.state.add(decl)
          val ack = solver.ack(noAttrs(decl))
          parser.state = state_
          (ack, this)

        case Push(depth) =>
          val ack = solver.ack(cmd)
          parser.push(depth)
          (ack, this)

        // the parser checks first that there are enough levels to pop
        case Pop(depth) =>
          parser.pop(depth)
          (solver.ack(cmd), this)

        case Reset =>
          val ack = solver.ack(cmd)
          parser.reset()
          (ack, this)

    // SMT-LIB does not admit attributes on declarations and definitions,
    // assertions are handled separately and keep theirs, e.g. for :named
    def noAttrs(decl: Decl): Decl =
      decl match
        case DeclareSort(con, _)              => DeclareSort(con, Attrs.empty)
        case DefineSort(con, params, body, _) => DefineSort(con, params, body, Attrs.empty)
        case DeclareDatatypes(cons, datas, _) => DeclareDatatypes(cons, datas, Attrs.empty)
        case DeclareFun(fun, _)               => DeclareFun(fun, Attrs.empty)
        case DefineFun(fun, body, _)          => DefineFun(fun, body, Attrs.empty)
        case _                                => decl
