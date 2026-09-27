package cuvee.pipe

import cuvee.Error

import cuvee.Name
import cuvee.sexpr._
import cuvee.core._

object Parser:
  def ack(from: Any): Ack =
    from match
      case Id("success") =>
        Ack.Success
      case Id("unsupported") =>
        Ack.Unsupported
      // case List(Id("error"), Str(msg)) =>
      //   Error.raise(msg)
      case _ =>
        Error.raise("invalid response", from)

  def issat(from: Any): Status =
    from match
      case Id("sat") =>
        Status.Sat
      case Id("unsat") =>
        Status.Unsat
      case Id("unknown") =>
        Status.Unknown
      // case List(Id("error"), Str(msg)) =>
      //   Error.raise(msg)
      case _ =>
        Error.raise("invalid status", from)

  def labels(from: Any): Labels =
    from match
      case List(Id("labels"), ids*) =>
        Labels(ids.toList.map { case Id(name) => name })
      // case List(Id("error"), Str(msg)) =>
      //   Error.raise(msg)
      case _ =>
        Error.raise("invalid labels", from)

class Parser(init: State):
  var state = init
  var stack: List[State] = List()

  def list[A](from: Seq[Any])(f: Any => A): List[A] =
    for arg <- from.toList
    yield f(arg)

  def cmd(from: Any): Cmd =
    from match
      // control commands

      case List(Id("set-logic"), Id(logic)) =>
        state = state.setLogic(logic)
        SetLogic(logic)

      case List(Id("set-option"), Kw(name), value) =>
        state = state.setOption(name, value)
        SetOption(name, value)

      case List(Id("get-info"), Kw(name)) =>
        GetInfo(name)

      case List(Id("set-info"), Kw(name), value) =>
        state = state.setInfo(name, value)
        SetInfo(name, value)

      case List(Id("get-model")) =>
        GetModel

      case List(Id("labels")) =>
        Labels

      case List(Id("check-sat")) =>
        CheckSat

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

      // sort and datatype declarations and definitions

      case List(Id("declare-sort"), Id(name), Num(digits), attrs*) =>
        val arity = digits.toInt
        val con = Con(name, arity)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(con, attrs_)
        DeclareSort(con, attrs_)

      case List(Id("define-sort"), Id(name), List(params*), body, attrs*) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val arity = params.length
        val con = Con(name, arity)

        val body_ = typ(scope, body)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(con, attrs_)
        state = state.define(con, params_, body_)
        DefineSort(con, params_, body_, attrs_)

      case List(Id("declare-datatypes"), _*) =>
        Error.raise("unsupported", from)

      // polymorphic Alt-Ergo .psmt declarations and definitions

      case List(Id("declare-const"), Id(name), List(Id("par"), List(params*), res, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val args_ = Nil
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, args_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(fun, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("declare-fun"), Id(name), List(Id("par"), List(params*), List(args*), res, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val args_ = list(args) { typ(scope, _) }
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, args_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(fun, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("define-fun"), Id(name), List(Id("par"), List(params*), List(formals*), res, body, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val formals_ = list(formals) { formal(scope, _) }
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_.types, res_)

        val expr_ = expr(scope ++ formals_, body)
        val body_ = Type.check(scope, expr_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(fun, attrs_)
        state = state.define(fun, formals_, body_)
        DefineFun(fun, formals_, body_, attrs_)

      // monomorphic SMT-LIB declarations and definitions

      case List(Id("declare-const"), Id(name), res, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val args_ = Nil
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, args_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(fun, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("declare-fun"), Id(name), List(args*), res, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val args_ = list(args) { typ(scope, _) }
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, args_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(fun, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("define-fun"), Id(name), List(formals*), res, body, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val formals_ = list(formals) { formal(scope, _) }
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_.types, res_)

        val expr_ = expr(scope ++ formals_, body)
        val body_ = Type.check(scope, expr_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(fun, attrs_)
        state = state.define(fun, formals_, body_)
        DefineFun(fun, formals_, body_, attrs_)

      // assertions and proof goals

      case List(Id("assert"), List(Id("par"), List(params*), phi, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)
        val expr_ = expr(scope, phi)
        val phi_ = Type.check(scope, expr_, Sort.bool)
        val attrs_ = annotation(attrs.toList)
        Assert(Axiom, params_, phi_, attrs_)

      case List(Id("assert"), phi, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty
        val expr_ = expr(scope, phi)
        val phi_ = Type.check(scope, expr_, Sort.bool)
        val attrs_ = annotation(attrs.toList)
        Assert(Axiom, params_, phi_, attrs_)

      // procedural fragment

      case List(Id("declare-proc"), Id(name), List(in*), List(out*), attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val in_ = list(in) { typ(scope, _) }
        val out_ = list(out) { typ(scope, _) }
        val proc = Proc(name, params_, in_, out_)

        val attrs_ = annotation(attrs.toList)

        state = state.declare(proc, attrs_)
        DeclareProc(proc, attrs_)

      case List(Id("define-proc"), Id(name), List(in*), List(out*), body, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val in_ = list(in) { formal(scope, _) }
        val out_ = list(out) { formal(scope, _) }
        val proc = Proc(name, params_, in_.types, out_.types)

        val body_ = prog(scope ++ in_ ++ out_, out_.toSet, body)

        val attrs_ = annotation(attrs.toList)

        state = state.declare(proc, attrs_)
        DefineProc(proc, in_, out_, body_, attrs_)

      case List(Id("declare-proc"), Id(name), List(Id("par"), List(params*), List(in*), List(out*), attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope.empty

        val in_ = list(in) { typ(scope, _) }
        val out_ = list(out) { typ(scope, _) }
        val proc = Proc(name, params_, in_, out_)

        val attrs_ = annotation(attrs.toList)

        state = state.declare(proc, attrs_)
        DeclareProc(proc, attrs_)

      case List(Id("define-proc"), Id(name), List(Id("par"), List(params*), List(in*), List(out*), body, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope.empty

        val in_ = list(in) { formal(scope, _) }
        val out_ = list(out) { formal(scope, _) }
        val proc = Proc(name, params_, in_.types, out_.types)

        val body_ = prog(scope ++ in_ ++ out_, out_.toSet, body)

        val attrs_ = annotation(attrs.toList)

        state = state.declare(proc, attrs_)
        DefineProc(proc, in_, out_, body_, attrs_)

      case _ =>
        Error.raise("not a command", from)

  def annotations(from: List[Any]): List[(String, Option[Any])] =
    from match
      case Nil =>
        Nil

      case Kw(kw) :: Nil =>
        List(kw -> None)

      case Kw(kw) :: (rest @ Kw(_) :: _) =>
        List(kw -> None) ++ annotations(rest)

      case Kw(kw) :: arg :: rest =>
        List(kw -> Some(arg)) ++ annotations(rest)

      case _ =>
        Error.raise("not an annotation", from)

  def annotation(from: List[Any]): Attrs =
    Attrs(annotations(from))

  def param(from: Any): Param =
    from match
      case Id(name) =>
        Param(name)

      case _ =>
        Error.raise("not a type parameter", from)

  def formal(scope: Scope, from: Any): Var =
    from match
      case List(Id(name), sort) =>
        Var(name, typ(scope, sort))

      case _ =>
        Error.raise("not a formal argument", from)

  def typ(scope: Scope, from: Any): Type =
    from match
      case Id(name) if scope.params.contains(name) =>
        scope.params(name)

      case Id(name) if state.sorts contains name =>
        Sort(state.sorts(name), Nil)

      case List(Id(name), args*) if state.sorts contains name =>
        val args_ = list(args) { typ(scope, _) }
        Sort(state.sorts(name), args_)

      case _ =>
        Error.raise("not a type", from)

  def app(scope: Scope, name: Name, args: List[Any]): Expr =
    val fun = state.funs((name, args.length))
    val args_ = list(args) { expr(scope, _) }

    val su = Subst.fresh(fun.params)
    val inst_ = su(fun.args)
    val typ_ = su(fun.res)
    App(fun, inst_, typ_, args_)

  def expr(scope: Scope, from: Any): Expr =
    from match
      case Num(digits) =>
        Lit(BigInt(digits), Sort.int)

      case Str(text) =>
        Lit(text, Sort.string)

      case Id(name) if scope.vars.contains(name) =>
        scope.vars(name)

      case Id(name) if state.funs.contains((name, 0)) =>
        app(scope, name, Nil)

      case List(Id(name), args*) if state.funs.contains((name, args.length)) =>
        app(scope, name, args.toList)

      case List(Id("forall"), List(bound*), body) =>
        val bound_ = list(bound) { formal(scope, _) }
        val scope_ = scope ++ bound_
        val body_ = expr(scope_, body)
        Forall(bound_, body_)

      case List(Id("exists"), List(bound*), body) =>
        val bound_ = list(bound) { formal(scope, _) }
        val scope_ = scope ++ bound_
        val body_ = expr(scope_, body)
        Forall(bound_, body_)

      case _ =>
        Error.raise("not an expression", from)

  def prog(scope: Scope, mod: Set[Var], from: Any): Prog =
    ???
