package cuvee.pipe

import cuvee.Config
import cuvee.Error
import cuvee.core._

// arguments: the configuration of the run, e.g. its printer, the state, which already encompasses the new commands,
// the commands passed so far, the new commands, and the command that flushes them, e.g. Done;
// the result: the commands in front of the flush, and the command that flushes them downstream, usually the same,
// none if the transform consumes it, e.g. Horn the verify-call (see Stage.query)
type Transform = (Config, State, List[Cmd], List[Cmd], Cmd) => (List[Cmd], Option[Cmd])

object Stage:
  def empty(config: Config, init: State, transform: Transform, next: Sink) =
    Stage(config, init, transform, Nil, Nil, Nil, init, next)

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

  def query(cmd: Cmd) =
    cmd match
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

        val (cmds, flush) = transform(config, state, prefix, pending, last)
        val (result, added, next_) =
          last match
            case Push(_) | Pop(_) | Reset | Done | Exit => next.query(cmds, last)
            case _ =>
              flush match
                case Some(flush) => next.query(cmds, flush)
                case None        => (Ack.Success, Nil, next.exec(cmds))

        val prefix_ = prefix ++ pending
        val rpending_ = Nil

        val stage_ = copy(prefix = prefix_, rpending = rpending_, next = next_)

        last match
          case Push(depth) => (result, added, stage_.push(depth))
          case Pop(depth)  => (result, added, stage_.pop(depth))
          case Reset       => (result, added, stage_.reset)
          case _           => (result, added, stage_)
