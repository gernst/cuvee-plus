package cuvee.smtlib

import cuvee.Name
import cuvee.Error
import cuvee.core._
import cuvee.sexpr.Attrs

object Printer extends cuvee.pipe.Printer:
  import cuvee.sexpr.Printer.escape
  import cuvee.sexpr.Printer.atom
  import cuvee.sexpr.Printer.list
  import cuvee.sexpr.Printer.flat
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
    list(arglists.flatten.toList)

  def sexprs(anys: List[Any]*): List[String] =
    for any <- anys.toList; line <- sexpr(any)
    yield line

  def str(value: String) =
    atom("\"" + value.replace("\"", "\\\"") + "\"")

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

  def attr(name: String, arg: Any): List[String] =
    arg match
      case None =>
        kw(name)

      // some attributes may have been resolved already
      case Some(res: Result) =>
        kw(name) ++ lines(res)

      case Some(cmd: Cmd) =>
        kw(name) ++ lines(cmd)

      case Some(typ: Type) =>
        kw(name) ++ lines(typ)

      case Some(expr: Expr) =>
        kw(name) ++ lines(expr)

      case Some(prog: Prog) =>
        kw(name) ++ lines(prog)

      case Some(arg) =>
        sexpr(arg)

  def lines(attrs: Attrs): List[String] =
    for
      (name, arg) <- attrs.attrs;
      line <- attr(name, arg)
    yield line

  def note(expr: Expr, attrs: Attrs) =
    if attrs.isEmpty
    then lines(expr)
    else apps(atom("!"), lines(expr), lines(attrs))

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

      case Labels(labels) =>
        apps(atom("labels"), labels)

      case error: cuvee.Error =>
        val info =
          for item <- error.info.toList; line <- str(item.toString)
          yield line

        apps(atom("error"), str(error.msg), info)

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

      case DeclareSort(Con(name, arity), attrs) =>
        apps(atom("declare-sort"), mangle(name), atom(arity.toString), lines(attrs))

      case DefineSort(Con(name, arity), params, body, attrs) =>
        apps(atom("define-sort"), mangle(name), list(lines(params)), lines(body), lines(attrs))

      case DeclareFun(Fun(name, Nil, args, res), attrs) =>
        apps(atom("declare-fun"), mangle(name), list(lines(args)), lines(res), lines(attrs))

      case DeclareFun(Fun(name, params, args, res), attrs) =>
        val body_ = apps(atom("par"), list(lines(params)), list(lines(args)), lines(res), lines(attrs))
        apps(atom("declare-fun"), mangle(name), body_)

      case DefineFun(Fun(name, Nil, args, res), bound, body, attrs) =>
        apps(atom("define-fun"), mangle(name), list(formals(bound)), lines(res), lines(body), lines(attrs))

      case DefineFun(Fun(name, params, args, res), bound, body, attrs) =>
        val body_ = apps(atom("par"), list(lines(params)), list(formals(bound)), lines(res), lines(body), lines(attrs))
        apps(atom("define-fun"), mangle(name), body_)

      case Assert(Axiom, Nil, phi, attrs) =>
        apps(atom("assert"), note(phi, attrs))

      case Assert(Axiom, params, phi, attrs) =>
        apps(atom("assert"), apps(atom("par"), list(lines(params)), note(phi, attrs)))

      case Assert(justify, params, phi, attrs) =>
        ???

      case DeclareProc(Proc(name, Nil, args, ret), attrs) =>
        apps(atom("declare-proc"), mangle(name), list(lines(args)), list(lines(ret)), lines(attrs))

      case DefineProc(Proc(name, Nil, args, ret), in, out, body, attrs) =>
        apps(atom("define-proc"), mangle(name), list(lines(args)), list(lines(ret)), lines(body), lines(attrs))

      case DeclareProc(Proc(name, params, args, ret), attrs) =>
        val body_ = apps(atom("par"), list(lines(args)), list(lines(ret)), lines(attrs))
        apps(atom("declare-proc"), mangle(name), body_)

      case DefineProc(Proc(name, params, args, ret), in, out, body, attrs) =>
        val body_ = apps(atom("par"), list(lines(args)), list(lines(ret)), lines(body), lines(attrs))
        apps(atom("define-proc"), mangle(name), list(lines(args)), list(lines(ret)), body_)

  def lines(typ: Type) =
    typ match
      case Param(name) =>
        mangle(name)

      case Sort(Con(name, arity), Nil) =>
        mangle(name)

      case Sort(Con(name, arity), args) =>
        apps(mangle(name), lines(args))

  def lines(expr: Expr) =
    expr match
      case Var(name, typ) =>
        mangle(name)

      case Lit(value: BigInt, typ) =>
        int(value)

      case Lit(value: String, typ) =>
        str(value)

      case Lit(_, _) =>
        Error.raise("unprintable literal", expr)

      case App(fun, inst, typ, Nil) =>
        mangle(fun.name)

      case App(fun, inst, typ, args) =>
        apps(mangle(fun.name), lines(args))

      case Bind(quant, bound, body) =>
        apps(mangle(quant), list(formals(bound)), lines(body))

      case Let(bound, args, body) =>
        apps(atom("let"), list(eqs(bound, args)), lines(body))

  def lines(prog: Prog): List[String] =
    prog match
      case Break =>
        apps(atom("break"))

      case Continue =>
        apps(atom("continue"))

      case Return =>
        apps(atom("break"))

      // case Spec(xs, pre, post) =>

      case Assign(lhs, rhs) =>
        apps(atom("assign"), eqs(lhs, rhs))

      case Call(proc, lhs, args) =>
        apps(atom("call"), mangle(proc), list(lines(lhs)), list(lines(args)))

      case Block(locals, progs) =>
        apps(mangle("block"), apps(mangle("locals"), formals(locals)), lines(progs))

      // case Choice(progs) =>
      // case If(test, left, right) =>
      // case While(test, body, attrs) =>
