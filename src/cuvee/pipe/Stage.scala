package cuvee.pipe

import cuvee.Config
import cuvee.Error
import cuvee.core._

// a stage of the pipeline, which transforms the commands at each flush (see Stage)
trait Transform:
  // arguments: the configuration of the run, e.g. its printer, the state, which already encompasses the new commands,
  // the commands passed so far, the new commands, and the command that flushes them, e.g. Done, none for a goal or
  // lemma, which is among the new commands;
  // the result: the commands in front of the flush, and the command that flushes them downstream, usually the same,
  // none if the transform consumes it, e.g. Horn the verify-call (see Stage.query)
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Option[Cmd]): (List[Cmd], Option[Cmd])

object Stage:
  def empty(config: Config, init: State, transform: Transform, next: Sink) =
    Stage(config, init, transform, Nil, Nil, Nil, init, next)

  // the answer to a goal or lemma from those to its outputs: incorrect if one of them is, correct if all are, also if
  // there are none, since a transform drops a goal only when it has reduced it to true, and unknown otherwise
  def combine(answers: List[Result]): Result =
    if answers.contains(Status.Incorrect) then Status.Incorrect
    else if answers.forall(_ == Status.Correct) then Status.Correct
    else Status.Unknown

case class Stage(
    config: Config,
    init: State,
    transform: Transform,
    stack: List[(List[Cmd], State)],
    prefix: List[Cmd],
    rpending: List[Decl],
    state: State,
    next: Sink
) extends Sink:
  def push(depth: Int) =
    Error.report("pipe not flushed"):
      require(rpending.isEmpty)
    copy(stack = List.fill(depth)((prefix, state)) ++ stack)

  def pop(depth: Int) =
    Error.report("pipe not flushed"):
      require(rpending.isEmpty)
    Error.report("cannot pop " + depth + " levels from stack of size " + stack.length):
      require(depth <= stack.length)
    if depth == 0 then this
    else
      val (prefix_, state_) = stack(depth - 1)
      copy(stack = stack.drop(depth), prefix = prefix_, state = state_)

  def reset =
    Error.report("pipe not flushed"):
      require(rpending.isEmpty)
    Stage.empty(config, init, transform, next)

  // the pending commands transformed and passed on, with the answers to the goals and lemmas among the outputs,
  // e.g. those of the procedures (VCGen)
  def flush: (List[Result], Stage) =
    if rpending.isEmpty
    then (Nil, this)
    else
      val pending = rpending.reverse
      val (cmds, _) = transform(config, state, prefix, pending, None)
      val (answers, next_) = next.query(cmds)
      (answers, copy(prefix = prefix ++ pending, rpending = Nil, next = next_))

  def query(cmd: Cmd) =
    cmd match
      // a goal or lemma that is not free is answered immediately: the pending commands are flushed in front of it,
      // whose answers come along, then it is transformed on its own, and its answer combines those to its outputs
      case goal @ Assert(Goal | Lemma, _, _, attrs) if !attrs.contains("free") =>
        val (added, stage) = flush
        val (cmds, _) = transform(config, state, stage.prefix, List(goal), None)
        val (answers, next_) = stage.next.query(cmds)
        (Stage.combine(answers), added, stage.copy(prefix = stage.prefix :+ goal, next = next_))

      case decl: Assert =>
        val stage_ = copy(rpending = decl :: rpending)
        (Ack.Success, Nil, stage_)

      case decl: Decl =>
        val stage_ = copy(rpending = decl :: rpending, state = state.add(decl))
        (Ack.Success, Nil, stage_)

      // push, pop, and reset change the stack of every stage, Done and Exit end the input for every sink, hence these
      // are passed on whatever the transform returns; another flush that the transform consumes is acknowledged
      case last =>
        val pending = rpending.reverse

        val (cmds, flush) = transform(config, state, prefix, pending, Some(last))
        val (result, added, next_) =
          last match
            case Push(_) | Pop(_) | Reset | Done | Exit => next.query(cmds, last)
            case _ =>
              flush match
                case Some(flush) => next.query(cmds, flush)
                case None =>
                  val (answers, next_) = next.query(cmds)
                  (Ack.Success, answers, next_)

        val prefix_ = prefix ++ pending
        val rpending_ = Nil

        val stage_ = copy(prefix = prefix_, rpending = rpending_, next = next_)

        last match
          case Push(depth) => (result, added, stage_.push(depth))
          case Pop(depth)  => (result, added, stage_.pop(depth))
          case Reset       => (result, added, stage_.reset)
          case _           => (result, added, stage_)
