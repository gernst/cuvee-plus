package cuvee.pipe

import cuvee.Error
import cuvee.core._
import cuvee.smtlib.Solver

// the answers of -verify, correct, incorrect, or unknown, whether the program satisfies its specification, i.e.,
// its contracts and loop invariants: each obligation is checked against the status that it has if the program is
// correct (see expected); it holds if the solver answers that status, it is refuted if it answers the opposite one,
// unless the goal is :abstract, i.e., stronger than the specification (a loop without invariant, see VCGen, or the
// encoding of -fallback), otherwise it is undecided; without a solver, only the goal false is refuted;
// the answer to verify-call is the outcome of the obligations so far, as is the answer to the end of the input
// if there was no verify-call; obligations are not thrown as errors, such that all commands are processed;
// the commands are passed to the solver directly, as by the solver sink, but without keeping track of the
// declarations, since models and the answers to get-info are not reported
object Verify:
  // incorrect if one of the outcomes is, otherwise unknown if one of them is
  def and(left: Status, right: Status) =
    if left == Status.Incorrect || right == Status.Incorrect then Status.Incorrect
    else if left == Status.Unknown || right == Status.Unknown then Status.Unknown
    else Status.Correct

  def sink(solver: Option[Solver]) =
    Verify(solver, Status.Correct, false)

  // the status of an obligation if the program satisfies its specification: goals and lemmas are checked by their
  // negation, which is unsat (see Solver.valid), the check-sat of the clauses of -chc is sat, since a model of the
  // clauses gives the invariants (see Horn); a check-sat of the input counts as well
  def expected(cmd: Cmd): Status =
    cmd match
      case CheckSat => Status.Sat
      case _        => Status.Unsat

  // the outcome of an obligation whose expected status is `expected`, given the answer `status`
  def outcome(expected: Status, status: Status, approximated: Boolean): Status =
    if status == expected then Status.Correct
    else if status == Status.Unknown || approximated then Status.Unknown
    else Status.Incorrect

// outcome: the aggregated outcome so far, correct, incorrect, or unknown,
// answered: whether a verify-call has been answered
case class Verify(solver: Option[Solver], outcome: Status, answered: Boolean) extends Sink:
  // the declarations that SMT-LIB has built in are not passed to the solver
  override def knows =
    if solver.nonEmpty then Set("smt2") else Set()

  // the acknowledgement of the solver, if there is one
  def ack(cmd: Cmd): Ack =
    solver match
      case Some(solver) => solver.ack(cmd)
      case None         => Ack.Success

  def query(cmd: Cmd) =
    cmd match
      // only the attributes :named and :pattern are passed on, as by the solver sink, free lemmas are assumed like
      // axioms
      case Assert(Axiom, params, phi, attrs) =>
        (ack(Assert(Axiom, params, phi, attrs.retain("named", "pattern"))), Nil, this)

      case Assert(Lemma, params, phi, attrs) if attrs.contains("free") =>
        (ack(Assert(Axiom, params, phi, attrs.retain("named", "pattern"))), Nil, this)

      // lemmas that hold are assumed subsequently
      case Assert(justify @ (Goal | Lemma), params, phi, attrs) =>
        val status =
          solver match
            case Some(solver)         => solver.valid(params, phi)
            case None if phi == False => Status.Sat
            case None                 => Status.Unknown

        if justify == Lemma && status == Status.Unsat
        then ack(Assert(Axiom, params, phi, attrs.retain("named", "pattern")))

        val outcome_ = Verify.and(outcome, Verify.outcome(Verify.expected(cmd), status, attrs.contains("abstract")))
        (Ack.Success, Nil, copy(outcome = outcome_))

      case CheckSat =>
        val status =
          solver match
            case Some(solver) => solver.check()
            case None         => Status.Unknown

        val outcome_ = Verify.and(outcome, Verify.outcome(Verify.expected(cmd), status, false))
        (status, Nil, copy(outcome = outcome_))

      case _: VerifyCall =>
        (outcome, Nil, copy(answered = true))

      // the end of the input is answered if there was no verify-call, otherwise it is acknowledged, such that the
      // answers to the queries added in front of it are not reported, e.g. the check-sat of Horn (see Pipe.run)
      case Done =>
        for solver <- solver do solver.destroy()
        if answered
        then (Ack.Success, Nil, this)
        else (outcome, Nil, this)

      case Exit =>
        val ack_ = ack(cmd)
        for solver <- solver do solver.destroy()
        (ack_, Nil, this)

      // the programs must have been verified, otherwise the input would be correct without checking anything
      case _: DeclareProc | _: DefineProc | _: DeclareVar | _: AnnotateTag =>
        Error.raise("-verify needs -vcgen, -teq, or -chc for procedures")

      // models and the answers to get-info and get-option are not reported
      case GetModel | _: GetInfo | _: GetOption =>
        (Ack.Done, Nil, this)

      case GetWitness | Labels =>
        (Ack.Unsupported, Nil, this)

      // an option that the solver does not know is unsupported (see Solver.option)
      case option: SetOption =>
        val ack_ =
          solver match
            case Some(solver) => solver.option(option)
            case None         => Ack.Success
        (ack_, Nil, this)

      case decl: Decl =>
        (ack(Solver.noAttrs(decl)), Nil, this)

      case Push(_) | Pop(_) | Reset =>
        (ack(cmd), Nil, this)
