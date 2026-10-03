package cuvee.pipe

import cuvee.Error
import cuvee.core._

// arguments: the commands passed so far, the new commands, the command that flushes them, e.g. Done,
// and the state, which already encompasses the new commands
type Transform = (List[Cmd], List[Cmd], Cmd, State) => List[Cmd]

object Stage:
  def empty(init: State, transform: Transform, next: Sink) =
    Stage(init, transform, Nil, Nil, Nil, init, next)

case class Stage(
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
    Stage.empty(init, transform, next)

  def query(cmd: Cmd) =
    cmd match
      case decl: Assert =>
        val stage_ = copy(rpending = decl :: rpending)
        (Ack.Success, stage_)

      case decl: Decl =>
        val stage_ = copy(rpending = decl :: rpending, state = state.add(decl))
        (Ack.Success, stage_)

      case last =>
        val pending = rpending.reverse

        val cmds = transform(prefix, pending, last, state)
        val (result, next_) = next.query(cmds, last)

        val prefix_ = prefix ++ pending
        val rpending_ = Nil

        val stage_ = copy(prefix = prefix_, rpending = rpending_, next = next_)

        last match
          case Push(depth) => (result, stage_.push(depth))
          case Pop(depth)  => (result, stage_.pop(depth))
          case Reset       => (result, stage_.reset)
          case _           => (result, stage_)
