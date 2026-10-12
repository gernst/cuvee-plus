package cuvee.pipe

import cuvee.core._
import cuvee.sexpr.Id
import cuvee.smtlib.Solver

// the answers of -verify, correct, incorrect, or unknown, whether the program satisfies its specification, i.e.,
// its contracts and loop invariants: each obligation is checked against its expected status, goals and lemmas are
// valid iff their negation is unsat, a check-sat expects the status of the set-info :status before it, e.g. sat for
// the clauses of -chc (see Horn); an obligation holds if the solver answers the expected status, it is refuted if it
// answers the opposite one, unless the goal is :abstract, i.e., stronger than the specification (a loop without
// invariant, see VCGen, or the encoding of -fallback), otherwise it is undecided; without a solver, only the goal
// false is refuted; check-sat without expected status is answered but does not count;
// the answer to verify-call is the outcome of the obligations so far, as is the answer to the end of the input
// if there was no verify-call; obligations are not thrown as errors, such that all commands are processed;
// the commands are passed to the solver directly, as by the solver sink of -check, but without keeping track of
// the declarations, since models and the answers to get-info are not reported
object Verify:
  // incorrect if one of the outcomes is, otherwise unknown if one of them is
  def and(left: Status, right: Status) =
    if left == Status.Incorrect || right == Status.Incorrect then Status.Incorrect
    else if left == Status.Unknown || right == Status.Unknown then Status.Unknown
    else Status.Correct

  def sink(solver: Option[Solver]) =
    Verify(solver, Status.Correct, None, false)

  // the outcome of an obligation whose expected status is `expected`, given the answer `status`
  def outcome(expected: Status, status: Status, approximated: Boolean): Status =
    if status == expected then Status.Correct
    else if status == Status.Unknown || approximated then Status.Unknown
    else Status.Incorrect

// outcome: the aggregated outcome so far, correct, incorrect, or unknown, expected: the status of the next
// check-sat, answered: whether a verify-call has been answered
case class Verify(solver: Option[Solver], outcome: Status, expected: Option[Status], answered: Boolean) extends Sink:
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

      // after a refutation, the answers are incorrect regardless of the remaining goals
      case Assert(Goal | Lemma, _, _, _) if outcome == Status.Incorrect =>
        (Ack.Success, Nil, this)

      // lemmas that hold are assumed subsequently
      case Assert(justify @ (Goal | Lemma), params, phi, attrs) =>
        val status =
          solver match
            case Some(solver)         => solver.valid(params, phi)
            case None if phi == False => Status.Sat
            case None                 => Status.Unknown

        if justify == Lemma && status == Status.Unsat
        then ack(Assert(Axiom, params, phi, attrs.retain("named", "pattern")))

        val outcome_ = Verify.and(outcome, Verify.outcome(Status.Unsat, status, attrs.contains("abstract")))
        (Ack.Success, Nil, copy(outcome = outcome_))

      // the expected status of the next check-sat, which is not passed to the solver, since z3 would report an error
      // for a check-sat that contradicts it; unknown is no expectation
      case SetInfo("status", Id(name @ ("sat" | "unsat"))) =>
        val expected_ = if name == "sat" then Status.Sat else Status.Unsat
        (Ack.Success, Nil, copy(expected = Some(expected_)))

      case SetInfo("status", _) =>
        (Ack.Success, Nil, copy(expected = None))

      case CheckSat =>
        val status =
          solver match
            case Some(solver) => solver.check()
            case None         => Status.Unknown

        val outcome_ =
          expected match
            case Some(expected) => Verify.and(outcome, Verify.outcome(expected, status, false))
            case None           => outcome

        (status, Nil, copy(outcome = outcome_, expected = None))

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

      // models and the answers to get-info and get-option are not reported
      case GetModel | _: GetInfo | _: GetOption =>
        (Ack.Done, Nil, this)

      // procedures and global variables must have been eliminated, e.g. with -vcgen, as for the solver sink
      case _: DeclareProc | _: DefineProc | _: DeclareVar | _: AnnotateTag | GetWitness | Labels =>
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
