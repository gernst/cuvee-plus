package cuvee.smtlib

import util.Name
import util.Rational
import cuvee.Error
import cuvee.core._
import cuvee.core.Attrs

object Printer extends cuvee.pipe.Printer:
  import cuvee.sexpr.Printer.escape
  import cuvee.sexpr.Printer.atom
  import cuvee.sexpr.Printer.list
  import cuvee.sexpr.Printer.flat
  import cuvee.sexpr.Printer.{lines => sexpr}

  def mangle(name: Name) =
    atom(escape(name.indexed))

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
    then app("-", (-value).toString)
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
        kw(name) ++ command(cmd)

      case Some(typ: Type) =>
        kw(name) ++ lines(typ)

      case Some(expr: Expr) =>
        kw(name) ++ lines(expr)

      case Some(prog: Prog) =>
        kw(name) ++ lines(prog)

      // e.g. the variables of a modifies attribute
      case Some(exprs: List[?]) if exprs.forall(_.isInstanceOf[Expr]) =>
        kw(name) ++ list(exprs.flatMap(expr => lines(expr.asInstanceOf[Expr])))

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

      // not reported
      case Ack.Done =>
        Nil

      case Status.Unknown =>
        atom("unknown")

      case Status.Sat =>
        atom("sat")

      case Status.Unsat =>
        atom("unsat")

      case Labels(labels) =>
        apps(atom("labels"), labels)

      case Info(attrs) =>
        list(lines(attrs))

      case Value(value) =>
        sexpr(value)

      case Model(decls) =>
        list(decls.flatMap(command))

      case error: Error =>
        val info =
          for item <- error.info.toList; line <- str(item.toString)
          yield line

        apps(atom("error"), str(error.msg), info)

  // each command is followed by an empty line
  def lines(cmd: Cmd): List[String] =
    command(cmd) :+ ""

  // a command without the empty line, e.g. inside a model or the value of an attribute
  // the attributes of declarations and definitions are dropped, which SMT-LIB does not have,
  // except for assertions, where they annotate the formula, and procedures, whose contracts they are
  def command(cmd: Cmd): List[String] =
    cmd match
      case CheckSat =>
        app("check-sat")

      case Labels =>
        app("labels")

      case GetModel =>
        app("get-model")

      case Exit =>
        app("exit")

      case Done =>
        Error.raise("internal command cannot be printed", cmd)

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

      case DeclareSort(Con(name, arity), _) =>
        apps(atom("declare-sort"), mangle(name), atom(arity.toString))

      case DeclareDatatypes(List(Con(name, _)), List(data), _) =>
        apps(atom("declare-datatype"), mangle(name), datatype(data))

      case DeclareDatatypes(cons, datas, _) =>
        val sigs_ =
          for Con(name, arity) <- cons
          yield apps(mangle(name), atom(arity.toString))

        val decls_ =
          for data <- datas
          yield datatype(data)

        apps(atom("declare-datatypes"), list(sigs_.flatten), list(decls_.flatten))

      case DefineSort(Con(name, arity), params, body, _) =>
        apps(atom("define-sort"), mangle(name), list(lines(params)), lines(body))

      // SMT-LIB declarations do not name the formal parameters
      case DeclareFun(Fun(name, Nil, formals, res), _) =>
        apps(atom("declare-fun"), mangle(name), list(lines(formals.types)), lines(res))

      case DeclareFun(Fun(name, params, formals, res), _) =>
        val body_ = apps(atom("par"), list(lines(params)), list(lines(formals.types)), lines(res))
        apps(atom("declare-fun"), mangle(name), body_)

      case DefineFun(Fun(name, Nil, formals, res), body, _) =>
        apps(atom("define-fun"), mangle(name), list(this.formals(formals)), lines(res), lines(body))

      case DefineFun(Fun(name, params, formals, res), body, _) =>
        val body_ = apps(atom("par"), list(lines(params)), list(this.formals(formals)), lines(res), lines(body))
        apps(atom("define-fun"), mangle(name), body_)

      case Assert(justify, Nil, phi, attrs) =>
        apps(atom(command(justify)), note(phi, attrs))

      case Assert(justify, params, phi, attrs) =>
        apps(atom(command(justify)), apps(atom("par"), list(lines(params)), note(phi, attrs)))

      // not part of SMT-LIB, but understood by z3
      case DeclareVar(Var(name, typ), _) =>
        apps(atom("declare-var"), mangle(name), lines(typ))

      // the formal parameters are named, since the contract may refer to them
      case DeclareProc(Proc(name, Nil, in, out), attrs) =>
        apps(atom("declare-proc"), mangle(name), list(formals(in)), list(formals(out)), lines(attrs))

      case DefineProc(Proc(name, Nil, in, out), body, attrs) =>
        apps(atom("define-proc"), mangle(name), list(formals(in)), list(formals(out)), lines(body), lines(attrs))

      case DeclareProc(Proc(name, params, in, out), attrs) =>
        val body_ = apps(atom("par"), list(lines(params)), list(formals(in)), list(formals(out)), lines(attrs))
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

  def datatype(data: Datatype) =
    val Datatype(params, constrs) = data

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

      case BitVec(n) =>
        app("_", "BitVec", n.toString)

  // functions that are not part of SMT-LIB are printed as their SMT-LIB counterparts,
  // indexed functions on bitvectors as indexed identifiers, e.g. (_ extract 7 0)
  def apply(fun: Fun) =
    if fun == Fun.eqv
    then atom("=")
    else if fun.name.name.startsWith("_ ")
    then List("(" + fun.name.name + ")")
    else mangle(fun.name)

  def lines(expr: Expr) =
    expr match
      case Var(name, typ) =>
        mangle(name)

      // bitvector literals in binary with all digits of the width
      case Lit(value: BigInt, BitVec(n)) =>
        atom("#b" + value.toString(2).reverse.padTo(n, '0').reverse)

      case Lit(value: BigInt, typ) =>
        int(value)

      case Lit(value: String, typ) =>
        str(value)

      case Lit(value: Rational, typ) if value.isNegative =>
        apps(atom("-"), lines(Lit(-value, typ)))

      // rationals that have no finite decimal expansion are written as fractions, (/ 1.0 3.0)
      case Lit(value: Rational, typ) =>
        value.decimal match
          case Some(digits) => atom(digits)
          case None         => apps(atom("/"), lines(Lit(Rational(value.num), typ)), lines(Lit(Rational(value.den), typ)))

      case Lit(_, _) =>
        Error.raise("unprintable literal", expr)

      // constant arrays need their type, which is not determined by the argument
      case App(Fun.const, inst, typ, List(arg)) =>
        apps(apps(atom("as"), atom("const"), lines(typ)), lines(arg))

      // polymorphic constants are annotated with their type, which is not determined by arguments
      case App(fun, inst, typ, Nil) if fun.params.nonEmpty =>
        apps(atom("as"), apply(fun), lines(typ))

      case App(fun, inst, typ, Nil) =>
        apply(fun)

      // nested conjunctions, disjunctions, sums, and products are flattened into a single application,
      // which the parser reads back as left-nested applications
      case And(phis) =>
        apps(apply(Fun.and), lines(phis))

      case Or(phis) =>
        apps(apply(Fun.or), lines(phis))

      case Plus.int(args) =>
        apps(apply(Fun.int.plus), lines(args))

      case Plus.real(args) =>
        apps(apply(Fun.real.plus), lines(args))

      case Times.int(args) =>
        apps(apply(Fun.int.times), lines(args))

      case Times.real(args) =>
        apps(apply(Fun.real.times), lines(args))

      case App(fun, inst, typ, args) =>
        apps(apply(fun), lines(args))

      case Distinct(exprs) =>
        apps(atom("distinct"), lines(exprs))

      case Is(expr, fun) =>
        apps(apps(atom("_"), atom("is"), mangle(fun.name)), lines(expr))

      // polymorphic constants are annotated already
      case As(App(fun, _, _, Nil), typ) if fun.params.nonEmpty =>
        apps(atom("as"), apply(fun), lines(typ))

      case As(expr, typ) =>
        apps(atom("as"), lines(expr), lines(typ))

      // not part of SMT-LIB, the combinators of trace equation systems, whose dependencies are bound like let
      case Trace(init, deps, acc, bound, update) =>
        apps(atom("trace"), apps(lines(acc), lines(init)), list(eqs(bound, deps)), lines(update))

      case Maps(deps, bound, update) =>
        apps(atom("map"), list(eqs(bound, deps)), lines(update))

      case Invs(deps, bound, body) =>
        apps(atom("all"), list(eqs(bound, deps)), lines(body))

      // not part of SMT-LIB, the choice of a result whose guard holds, (eps (phi1 expr1) ... (phin exprn))
      case Eps(updates) =>
        apps(atom("eps"), updates.flatMap(upd => apps(lines(upd.cond), lines(upd.rhs))))

      // not part of SMT-LIB, the value at the entry of the procedure
      case Old(expr) =>
        apps(atom("old"), lines(expr))

      // not part of SMT-LIB, the derivative with respect to xs is written (diff (xs) expr)
      case Diff(xs, expr) =>
        apps(atom("diff"), list(lines(xs)), lines(expr))

      case Bind(quant, bound, body) =>
        apps(mangle(quant), list(formals(bound)), lines(body))

      case Let(bound, args, body) =>
        apps(atom("let"), list(eqs(bound, args)), lines(body))

      // conditions of the cases are not part of SMT-LIB
      case Match(arg, cases) =>
        Error.report("match with conditions not supported in SMT-LIB", expr):
          require(cases.forall(_.cond == True))
        apps(atom("match"), lines(arg), list(for Case(pat, body, _) <- cases; line <- apps(lines(pat), lines(body)) yield line))

  def lines(prog: Prog): List[String] =
    prog match
      case Break =>
        apps(atom("break"))

      case Continue =>
        apps(atom("continue"))

      case Return =>
        apps(atom("return"))

      case Spec(Nil, False, True) =>
        apps(atom("abort"))

      case Spec(Nil, True, phi) =>
        apps(atom("assume"), lines(phi))

      case Spec(Nil, phi, True) =>
        apps(atom("assert"), lines(phi))

      case Spec(xs, True, True) =>
        apps(atom("havoc"), lines(xs))

      case Spec(xs, pre, post) =>
        apps(atom("spec"), list(lines(xs)), lines(pre), lines(post))

      case Assign(lhs, rhs) =>
        apps(atom("assign"), eqs(lhs, rhs))

      case Call(proc, args, res) =>
        apps(atom("call"), mangle(proc), list(lines(args)), list(lines(res)))

      case Block(locals, progs) =>
        apps(mangle("block"), apps(mangle("locals"), formals(locals)), lines(progs))

      case Choice(progs) =>
        apps(atom("choose"), lines(progs))

      case If(test, left, right) =>
        apps(atom("if"), lines(test), lines(left), lines(right))

      case While(test, body, attrs) =>
        apps(atom("while"), lines(test), lines(body), lines(attrs))

      case Iter(body, attrs) =>
        apps(atom("iter"), lines(body), lines(attrs))

      case Ode(time, xs, rhs, dom, attrs) =>
        apps(atom("ode"), lines(time), list(eqs(xs, rhs)), lines(dom), lines(attrs))

      // not part of SMT-LIB, the calls in parallel, (par (call ...) ...)
      case Par(calls) =>
        apps(atom("par"), lines(calls))
