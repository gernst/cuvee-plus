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
    list(args.toList)

  def apps(arglists: List[String]*): List[String] =
    list(arglists.flatten.toList)

  def sexprs(anys: List[Any]*): List[String] =
    for any <- anys.toList; line <- sexpr(any)
    yield line

  def str(value: String) =
    atom(cuvee.sexpr.Printer.str(value))

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
        kw(name) ++ sexpr(arg)

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

      case Push(depth) =>
        app("push", depth.toString)

      case Pop(depth) =>
        app("pop", depth.toString)

      case Reset =>
        app("reset")

      case SetLogic(name) =>
        app("set-logic", name)

      case GetOption(name) =>
        apps(atom("get-option"), kw(name))

      case SetOption(name, value) =>
        apps(atom("set-option"), kw(name), sexpr(value))

      case GetInfo(name) =>
        apps(atom("get-info"), kw(name))

      case SetInfo(name, value) =>
        apps(atom("set-info"), kw(name), sexpr(value))

      case DeclareSort(Con(name, arity), attrs) =>
        apps(atom("declare-sort"), mangle(name), atom(arity.toString), lines(attrs))

      case DeclareDatatype(Con(name, arity), params, constrs, attrs) =>
        apps(atom("declare-datatype"), mangle(name), datatype(params, constrs), lines(attrs))

      case DeclareDatatypes(datatypes) =>
        val sigs_ =
          for DeclareDatatype(Con(name, arity), _, _, _) <- datatypes
          yield apps(mangle(name), atom(arity.toString))

        val decls_ =
          for DeclareDatatype(_, params, constrs, _) <- datatypes
          yield datatype(params, constrs)

        apps(atom("declare-datatypes"), list(sigs_.flatten), list(decls_.flatten))

      case DefineSort(Con(name, arity), params, body, attrs) =>
        apps(atom("define-sort"), mangle(name), list(lines(params)), lines(body), lines(attrs))

      // SMT-LIB declarations do not name the formal parameters
      case DeclareFun(Fun(name, Nil, formals, res), attrs) =>
        apps(atom("declare-fun"), mangle(name), list(lines(formals.types)), lines(res), lines(attrs))

      case DeclareFun(Fun(name, params, formals, res), attrs) =>
        val body_ = apps(atom("par"), list(lines(params)), list(lines(formals.types)), lines(res), lines(attrs))
        apps(atom("declare-fun"), mangle(name), body_)

      case DefineFun(Fun(name, Nil, formals, res), body, attrs) =>
        apps(atom("define-fun"), mangle(name), list(this.formals(formals)), lines(res), lines(body), lines(attrs))

      case DefineFun(Fun(name, params, formals, res), body, attrs) =>
        val body_ = apps(atom("par"), list(lines(params)), list(this.formals(formals)), lines(res), lines(body), lines(attrs))
        apps(atom("define-fun"), mangle(name), body_)

      case Assert(justify, Nil, phi, attrs) =>
        apps(atom(command(justify)), note(phi, attrs))

      case Assert(justify, params, phi, attrs) =>
        apps(atom(command(justify)), apps(atom("par"), list(lines(params)), note(phi, attrs)))

      case DeclareProc(Proc(name, Nil, in, out), attrs) =>
        apps(atom("declare-proc"), mangle(name), list(lines(in.types)), list(lines(out.types)), lines(attrs))

      case DefineProc(Proc(name, Nil, in, out), body, attrs) =>
        apps(atom("define-proc"), mangle(name), list(formals(in)), list(formals(out)), lines(body), lines(attrs))

      case DeclareProc(Proc(name, params, in, out), attrs) =>
        val body_ = apps(atom("par"), list(lines(params)), list(lines(in.types)), list(lines(out.types)), lines(attrs))
        apps(atom("declare-proc"), mangle(name), body_)

      case DefineProc(Proc(name, params, in, out), body, attrs) =>
        val body_ = apps(atom("par"), list(lines(params)), list(formals(in)), list(formals(out)), lines(body), lines(attrs))
        apps(atom("define-proc"), mangle(name), body_)

  // goals and lemmas are not part of SMT-LIB, they are printed like assertions with their own command
  def command(justify: Justify) =
    justify match
      case Axiom => "assert"
      case Goal  => "goal"
      case Lemma => "lemma"

  def datatype(params: List[Param], constrs: List[(Fun, List[Fun])]) =
    val lines_ =
      for (constr, sels) <- constrs
      yield
        val sels_ =
          for
            sel <- sels
            line <- apps(mangle(sel.name), lines(sel.res))
          yield line

        apps(mangle(constr.name), sels_)

    if params.nonEmpty
    then apps(atom("par"), list(lines(params)), list(lines_.flatten))
    else list(lines_.flatten)

  def lines(typ: Type) =
    typ match
      case Param(name) =>
        mangle(name)

      case Sort(Con(name, arity), Nil) =>
        mangle(name)

      case Sort(Con(name, arity), args) =>
        apps(mangle(name), lines(args))

  // functions that are not part of SMT-LIB are printed as their SMT-LIB counterparts
  def apply(fun: Fun) =
    fun.name match
      case Name("<=>", None) => atom("=")
      case name              => mangle(name)

  def lines(expr: Expr) =
    expr match
      case Var(name, typ) =>
        mangle(name)

      case Lit(value: BigInt, typ) =>
        int(value)

      case Lit(value: String, typ) =>
        str(value)

      case Lit(value: BigDecimal, typ) if value < 0 =>
        app("-", value.abs.bigDecimal.toPlainString)

      case Lit(value: BigDecimal, typ) =>
        atom(value.bigDecimal.toPlainString)

      case Lit(_, _) =>
        Error.raise("unprintable literal", expr)

      case App(fun, inst, typ, Nil) =>
        apply(fun)

      case App(fun, inst, typ, args) =>
        apps(apply(fun), lines(args))

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
        apps(atom("return"))

      // case Spec(xs, pre, post) =>

      case Assign(lhs, rhs) =>
        apps(atom("assign"), eqs(lhs, rhs))

      case Call(proc, args, res) =>
        apps(atom("call"), mangle(proc), list(lines(args)), list(lines(res)))

      case Block(locals, progs) =>
        apps(mangle("block"), apps(mangle("locals"), formals(locals)), lines(progs))

      // case Choice(progs) =>
      // case If(test, left, right) =>
      // case While(test, body, attrs) =>
