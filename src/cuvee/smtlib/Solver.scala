package cuvee.smtlib

import util.Tool

import cuvee.Debug
import cuvee.Error

import cuvee.core._
import cuvee.core.Attrs
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

  // the command in SMT-LIB, line by line
  def write(cmd: Cmd) =
    for (line <- Printer.lines(cmd))
    do
      Debug.info("solver", proc.pid.toString + "> " + line)
      out.println(line)
    out.flush()

  // the response to `query` as an s-expression, errors reported by the solver are raised
  def read(query: Cmd): Any =
    Error.report("solver terminated unexpectedly", cmd):
      require(responses.nonEmpty)

    val (from, rest) =
      Error.report("invalid solver response"):
        Grammar.sexpr.parse(responses)

    responses = rest
    Debug.info("solver", proc.pid.toString + "< " + cuvee.sexpr.Printer.lines(from).mkString(" "))

    from match
      case List(Id("error"), Str(msg)) =>
        Error.raise("solver error", query, msg)

      case _ =>
        from

  // the response to `cmd`, each command is answered by one s-expression since print-success is set
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

  // run f in a fresh scope that is popped afterwards, even if f fails,
  // unless the solver has terminated, which is reported instead of the failure of pop
  def scoped[A](f: => A): A =
    push()
    try f
    finally
      if proc.isAlive
      then pop()
      else Error.raise("solver terminated unexpectedly", cmd.head, proc.exitValue)

  // the answer to check-sat
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

  def sink(solver: Solver, init: State) =
    Sink(init, solver)

  // a sink that passes commands to the solver,
  // goals and lemmas are proved first and must be valid, lemmas are asserted subsequently,
  // the parser keeps track of the declarations known to the solver, starting from `init`,
  // and interprets the answers to queries in that state
  // the declarations that SMT-LIB has built in ({:smt2}, see the preludes) are not passed to the solver,
  // all others are, without their attributes, e.g. those of higher-order features ({:ho}), which a solver may reject;
  // goals that do not hold are reported in SMT-LIB
  class Sink(init: State, solver: Solver) extends cuvee.pipe.Sink:
    val parser = new Parser(init)
    val printer = Printer

    override def knows =
      Set("smt2")

    // the answer to the last check-sat, a model is available only if it is sat
    var status: Option[Status] = None

    def query(cmd: Cmd) =
      cmd match
        // only the attributes :named and :pattern are passed on, the solvers reject unknown ones, e.g. :rw
        case Assert(Axiom, params, phi, attrs) =>
          (solver.ack(Assert(Axiom, params, phi, attrs.retain("named", "pattern"))), Nil, this)

        // lemmas with the attribute :free are assumed without proof, like axioms,
        // although they are meant to follow from the theory, e.g. lemmas whose proof is left to another tool
        case Assert(Lemma, params, phi, attrs) if attrs.contains("free") =>
          (solver.ack(Assert(Axiom, params, phi, attrs.retain("named", "pattern"))), Nil, this)

        // the solver's answer is reported if the goal is not valid, i.e., sat or unknown
        case Assert(justify, params, phi, attrs) =>
          val status = solver.valid(params, phi)
          if status != Status.Unsat then
            Error.raise(justify.toString.toLowerCase + " does not hold", status, printer.lines(phi).map(_.trim).mkString(" "))

          if justify == Lemma
          then solver.ack(Assert(Axiom, params, phi, attrs.retain("named", "pattern")))

          (Ack.Success, Nil, this)

        case CheckSat =>
          val status_ = solver.check()
          status = Some(status_)
          (status_, Nil, this)

        // procedures and global variables are not understood by SMT solvers and must have been eliminated, e.g. with -vcgen,
        // in particular, z3 accepts declare-var but does not acknowledge it with print-success
        case _: DeclareProc | _: DefineProc | _: DeclareVar | _: AnnotateTag =>
          (Ack.Unsupported, Nil, this)

        // the witnesses of SV-LIB are not produced
        case GetWitness =>
          (Ack.Unsupported, Nil, this)

        // the obligations of a verify-call have been checked already (see VCGen and Horn), it has no answer of its own
        case _: VerifyCall =>
          (Ack.Done, Nil, this)

        case _: GetInfo =>
          (Parser.info(solver.query(cmd)), Nil, this)

        case _: GetOption =>
          (Parser.value(solver.query(cmd)), Nil, this)

        case Labels =>
          (Parser.labels(solver.query(cmd)), Nil, this)

        // no answer if there is no model, e.g. to the get-model added by Horn when the clauses are unsat
        case GetModel if status != Some(Status.Sat) =>
          (Ack.Done, Nil, this)

        // a model that cannot be read is an error of the pipeline (see Pipe.run), the answer to check-sat before it
        // has been reported already
        case GetModel =>
          (parser.model(solver.query(cmd)), Nil, this)

        case Exit =>
          val ack = solver.ack(cmd)
          solver.destroy()
          (ack, Nil, this)

        case Done =>
          solver.destroy()
          (Ack.Done, Nil, this)

        // an option that the solver does not know is unsupported, as SMT-LIB prescribes, which z3 reports as an error,
        // e.g. :produce-witnesses of SV-LIB
        case option: SetOption =>
          parser.state = parser.state.add(option)
          val ack =
            try solver.ack(option)
            catch case error: Error if error.msg == "solver error" => Ack.Unsupported
          (ack, Nil, this)

        // the state is updated only once the solver has accepted the declaration,
        // attributes are kept in the state but not sent to the solver
        case decl: Decl =>
          val state_ = parser.state.add(decl)
          val ack = solver.ack(noAttrs(decl))
          parser.state = state_
          (ack, Nil, this)

        case Push(depth) =>
          val ack = solver.ack(cmd)
          parser.push(depth)
          (ack, Nil, this)

        // the parser checks first that there are enough levels to pop
        case Pop(depth) =>
          parser.pop(depth)
          (solver.ack(cmd), Nil, this)

        case Reset =>
          val ack = solver.ack(cmd)
          parser.reset()
          (ack, Nil, this)

    // SMT-LIB does not admit attributes on declarations and definitions,
    // assertions are handled separately and keep their names
    def noAttrs(decl: Decl): Decl =
      decl match
        case DeclareSort(con, _)              => DeclareSort(con, Attrs.empty)
        case DefineSort(con, params, body, _) => DefineSort(con, params, body, Attrs.empty)
        case DeclareDatatypes(cons, datas, _) => DeclareDatatypes(cons, datas, Attrs.empty)
        case DeclareFun(fun, _)               => DeclareFun(fun, Attrs.empty)
        case DefineFun(fun, body, _)          => DefineFun(fun, body, Attrs.empty)
        case _                                => decl
