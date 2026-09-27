package cuvee.dafny

import cuvee.core
import cuvee.core.State
import cuvee.core.Scope

class Parser(init: State):
  var state = init

  var stack: List[State] = List()

  def list[A, B](from: List[A])(f: A => B): List[B] =
    for arg <- from.toList
    yield f(arg)

  def resolve(scope: Scope, formal: (String, Type)): core.Var =
    val (name, typ) = formal
    state.formal(name, resolve(scope, typ))

  def resolve(scope: Scope, typ: Type): core.Type =
    typ match
      case Sort(name, Nil) if scope.params.contains(name) =>
        scope.params(name)

      case Sort(con, args) =>
        val args_ = list(args) { resolve(scope, _) }
        state.sort(con, args_)

  def resolve(scope: Scope, expr: Expr): core.Expr =
    expr match
      case Num(value) =>
        state.num(BigInt(value))

      case Str(value) =>
        state.str(value)

      case App(name, Nil, Nil) if scope.vars.contains(name) =>
        scope.vars(name)

      case App(fun, args, access) =>
        ???
        val args_ = list(args) { resolve(scope, _) }
        state.app(fun, args_)

      case Ex(bound, body) =>
        val bound_ = list(bound) { resolve(scope, _) }
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.ex(bound_, body_)

      case All(bound, body) =>
        val bound_ = list(bound) { resolve(scope, _) }
        val scope_ = scope ++ bound_
        val body_ = resolve(scope_, body)
        state.all(bound_, body_)

      case Let(vars, args, body) =>
        ???
