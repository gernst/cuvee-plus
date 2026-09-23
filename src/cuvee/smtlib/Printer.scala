package cuvee.smtlib

import cuvee.Name
import cuvee.core._
import cuvee.sexpr.Attrs

// case class Labels(labels: List[String]) extends Result

object Printer extends cuvee.Printer:
  import cuvee.sexpr.Printer.escape
  import cuvee.sexpr.Printer.atom
  import cuvee.sexpr.Printer.list
  import cuvee.sexpr.Printer.{lines => sexpr}

  def mangle(name: Name) =
    name match
      case Name(name, None) =>
        atom(escape(name))

      case Name(name, Some(index)) =>
        atom(escape(name + "$" + index))

  def app(args: String*): List[String] =
    app(args.toString)

  def apps(arglists: List[String]*): List[String] =
    for args <- arglists.toList; line <- list(args)
    yield line

  def sexprs(anys: List[Any]*): List[String] =
    for any <- anys.toList; line <- sexpr(any)
    yield line

  def int(value: BigInt) =
    if value < 0
    then app("-", value.toString)
    else atom(value.toString)

  def kw(name: String) =
    atom(":" + name)

  def formals(vars: List[Var]) =
    for Var(name, typ) <- vars; line <- apps(mangle(name), lines(typ))
    yield line

  def eqs(vars: List[Var], args: List[Expr]) =
    for (x, e) <- vars.zip(args); line <- apps(lines(x), lines(e))
    yield line

  def note(expr: Expr, attrs: Attrs) =
    if attrs.isEmpty
    then lines(expr)
    else apps(atom("!"), lines(expr), sexprs(attrs.flatten))

  def lines(res: Result) =
    res match
      case Ack.Success =>
        atom("success")

      case Ack.Unsupported =>
        atom("unsupported")

      case Status.Unknown =>
        atom("unknown")

      case Status.Sat =>
        atom("sat")

      case Status.Unsat =>
        atom("unsat")

  def lines(cmd: Cmd) =
    cmd match
      case CheckSat =>
        app("check-sat")

      case Labels =>
        app("labels")

      case GetModel =>
        app("get-model")

      case Exit =>
        app("exit")

      case Push =>
        app("push")

      case Pop =>
        app("pop")

      case Reset =>
        app("reset")

      case SetLogic(name) =>
        app("set-logic", name)

      case GetOption(name) =>
        apps(atom("get-option"), kw(name))

      case SetOption(name, value) =>
        apps(atom("set-option"), kw(name), sexpr(value))

      case GetInfo(name) =>
        apps(atom("get-option"), kw(name))

      case SetInfo(name, value) =>
        apps(atom("set-info"), kw(name), sexpr(value))

      case DeclareSort(Con(name, arity)) =>
        apps(atom("declare-sort"), mangle(name), atom(arity.toString))

      case DefineSort(Con(name, arity), params, body) =>
        apps(atom("define-sort"), mangle(name), list(lines(params)), lines(body))

      case DeclareFun(Fun(name, Nil, args, res)) =>
        apps(atom("declare-fun"), mangle(name), list(lines(args)), lines(res))

      case DeclareFun(Fun(name, params, args, res)) =>
        apps(atom("declare-fun"), mangle(name), apps(atom("par"), list(lines(params)), list(lines(args)), lines(res)))

      case DefineFun(Fun(name, Nil, args, res), bound, body) =>
        apps(atom("define-fun"), mangle(name), list(formals(bound)), lines(res), lines(body))

      case DefineFun(Fun(name, params, args, res), bound, body) =>
        apps(atom("define-fun"), mangle(name), apps(atom("par"), list(lines(params)), list(formals(bound)), lines(res), lines(body)))

      case Assert(Axiom, Nil, phi, attrs) =>
        apps(atom("assert"), note(phi, attrs))

      case Assert(Axiom, params, phi, attrs) =>
        apps(atom("assert"), apps(atom("par"), list(lines(params)), note(phi, attrs)))

      case Assert(justify, params, phi, attrs) =>
        ???

  def lines(typ: Type) =
    typ match
      case Param(name) =>
        mangle(name)

      case Sort(Con(name, arity), args) =>
        apps(mangle(name), lines(args))

  def lines(expr: Expr) =
    expr match
      case Var(name, typ) =>
        mangle(name)

      case Lit(value: BigInt, typ) =>
        int(value)

      case App(fun, inst, Nil) =>
        mangle(fun.name)

      case App(fun, inst, args) =>
        apps(mangle(fun.name), lines(args))

      case Bind(quant, bound, body) =>
        apps(mangle(quant), list(formals(bound)), lines(body))

      case Let(bound, args, body) =>
        apps(atom("let"), list(eqs(bound, args)), lines(body))
