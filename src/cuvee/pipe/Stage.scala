package cuvee.pipe

import scala.annotation.nowarn

import cuvee.Error
import cuvee.smtlib._

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
  def push =
    Error.abortIf("pipe not flushed", rpending.nonEmpty)
    copy(stack = (prefix, state) :: stack)

  def pop =
    Error.abortIf("pipe not flushed", rpending.nonEmpty)
    Error.reportIf("cannot pop", stack.isEmpty)
    @nowarn val (prefix_, state_) :: stack_ = stack
    copy(stack = stack_, prefix = prefix_, state = state_)

  def reset =
    Error.abortIf("pipe not flushed", rpending.nonEmpty)
    Stage.empty(init, transform, next)

  def query(cmd: Cmd) =
    cmd match
      case decl: Decl =>
        val stage_ = copy(rpending = decl :: rpending, state = state.add(decl))
        (Ack.Success, stage_)

      case last =>
        val pending = rpending.reverse

        val cmds = transform(prefix, pending, state)
        val (result, next_) = next.query(cmds, last)

        val prefix_ = prefix ++ pending
        val rpending_ = Nil

        val stage_ = copy(prefix = prefix_, rpending = rpending_, next = next_)

        last match
          case Push  => (result, stage_.push)
          case Pop   => (result, stage_.pop)
          case Reset => (result, stage_.reset)
          case _     => (result, stage_)
