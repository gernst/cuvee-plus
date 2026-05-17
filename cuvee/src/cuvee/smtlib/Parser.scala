package cuvee.smtlib

import cuvee.Error

import cuvee.Name
import cuvee.sexpr._
import cuvee.smtlib._
import cuvee.pure._

object Parser:
  def ack(from: Any): Ack =
    from match
      case Id("success") =>
        Ack.Success
      case Id("unsupported") =>
        Ack.Unsupported
      // case List(Id("error"), Str(msg)) =>
      //   Error.report(msg)
      case _ =>
        Error.report("invalid response: " + from)

  def issat(from: Any): Status =
    from match
      case Id("sat") =>
        Status.Sat
      case Id("unsat") =>
        Status.Unsat
      case Id("unknown") =>
        Status.Unknown
      // case List(Id("error"), Str(msg)) =>
      //   Error.report(msg)
      case _ =>
        Error.report("invalid status: " + from)

  def labels(from: Any): Labels =
    from match
      case List(Id("labels"), ids*) =>
        Labels(ids.toList.map { case Id(name) => name })
      // case List(Id("error"), Str(msg)) =>
      //   Error.report(msg)
      case _ =>
        Error.report("invalid labels: " + from)

class Parser(init: State):
  var state = init
  var stack: List[State] = List()

  def cmd(from: Any): Cmd =
    from match
      case List(Id("set-logic"), Id(logic)) =>
        SetLogic(logic)

      case List(Id("set-option"), Kw(attr), arg) =>
        SetOption(attr, arg)

      case List(Id("get-info"), Kw(attr)) =>
        GetInfo(attr)

      case List(Id("set-info"), Kw(attr)) =>
        SetInfo(attr, None)

      case List(Id("set-info"), Kw(attr), arg) =>
        SetInfo(attr, Some(arg))

      case List(Id("get-model")) => GetModel
      case List(Id("labels"))    => Labels

      case List(Id("check-sat")) => CheckSat

      case List(Id("push")) =>
        stack = state :: stack
        Push

      case List(Id("pop")) =>
        state = stack.head
        stack = stack.tail
        Pop

      case List(Id("reset")) =>
        state = init
        stack = List()
        Reset

      case List(Id("exit")) =>
        Exit

      // case List(Id("declare-sort"), Id(name), Num(digits)) =>
      //   val con = Con(name, digits.toInt)
      //   DeclareSort(con)

  def exprs(scope: Scope, from: Seq[Any]): List[Expr] =
    for arg <- from.toList
    yield expr(scope, arg)

  def expr(scope: Scope, from: Any): Expr =
    from match
      // case Num(digits) =>
      //   Lit(BigInt(digits), Sort.int)

      // case Dec(digits) =>
      //   Lit(digits.toDouble, Sort.real)

      case Id(name) if scope.bound.contains(name) =>
        Var(name, scope.bound(name))

      case Id(name) if state.funs.contains(name) =>
        ???

      case List(Id(name), args*) if state.funs.contains(name) =>
        val fun = state.funs(name)
        val args_ = exprs(scope, args)
        App(fun, ???, args_)
