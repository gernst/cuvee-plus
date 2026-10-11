package cuvee.smtlib

import cuvee.Error

import util.Name
import util.Rational
import cuvee.sexpr._
import cuvee.core._
// the numerals of s-expressions, not the literals of the core (core.Num)
import cuvee.sexpr.Num

object Parser:
  def ack(from: Any): Ack =
    from match
      case Id("success") =>
        Ack.Success
      case Id("unsupported") =>
        Ack.Unsupported
      case List(Id("error"), Str(msg)) =>
        Error.raise("solver error", msg)
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
      case List(Id("error"), Str(msg)) =>
        Error.raise("solver error", msg)
      case _ =>
        Error.raise("invalid status", from)

  def labels(from: Any): Labels =
    from match
      case List(Id("labels"), ids*) =>
        val names =
          for id <- ids.toList
          yield id match
            case Id(name) => name
            case _        => Error.raise("invalid label", id)
        Labels(names)
      case List(Id("error"), Str(msg)) =>
        Error.raise("solver error", msg)
      case _ =>
        Error.raise("invalid labels", from)

  // answer to get-info
  def info(from: Any): Result =
    from match
      case Id("unsupported") =>
        Ack.Unsupported
      case List(attrs*) =>
        Info(annotation(attrs.toList))
      case _ =>
        Error.raise("invalid info", from)

  // answer to get-option
  def value(from: Any): Result =
    from match
      case Id("unsupported") =>
        Ack.Unsupported
      case _ =>
        Value(from)

  // the keyword of a command or program, e.g. in errors, instead of the whole s-expression
  def head(from: Any): Any =
    from match
      case List(head, _*) => head
      case _              => from

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

  // a statement with a tag of SV-LIB, a procedure body or a loop: the scope of its variables, that of a contract if
  // it is the body of a procedure, the tag of the body of the enclosing procedure, and the variables whose values at
  // the entry of the procedure are available there, to which (at x tag) of SV-LIB refers (see svlib.Parser)
  case class Tagged(scope: Scope, contract: Option[Scope], body: Option[Name], entry: Set[Name])

class Parser(private var init: State):
  import Parser.annotation
  import Parser.Tagged

  var state = init
  var stack: List[State] = List()

  // the statements with a tag of SV-LIB, in the order of their occurrence, which annotate-tag commands refer to
  var tags: Map[Name, List[Tagged]] = Map()

  def record(tag: Name, tagged: Tagged): Unit =
    tags = tags + (tag -> (tags.getOrElse(tag, Nil) :+ tagged))

  def list[A](from: Seq[Any])(f: Any => A): List[A] =
    for arg <- from.toList
    yield f(arg)

  def push(depth: Int): Cmd =
    stack = List.fill(depth)(state) ++ stack
    Push(depth)

  def pop(depth: Int): Cmd =
    Error.report("cannot pop " + depth + " levels from stack of size " + stack.length):
      require(depth <= stack.length)

    if depth > 0 then
      state = stack(depth - 1)
      stack = stack.drop(depth)
    Pop(depth)

  def reset(): Cmd =
    state = init
    stack = List()
    Reset

  // the current state becomes the one that reset returns to
  def resetPoint() =
    init = state

  def cmd(from: Any): Cmd =
    from match
      // control commands

      case List(Id("set-logic"), Id(logic)) =>
        state = state.setLogic(logic)
        SetLogic(logic)

      case List(Id("set-option"), Kw(name), value) =>
        state = state.setOption(name, value)
        SetOption(name, value)

      case List(Id("get-option"), Kw(name)) =>
        GetOption(name)

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
        push(1)

      case List(Id("push"), Num(digits)) =>
        push(digits.toInt)

      case List(Id("pop")) =>
        pop(1)

      case List(Id("pop"), Num(digits)) =>
        pop(digits.toInt)

      case List(Id("reset")) =>
        reset()

      case List(Id("exit")) =>
        Exit

      // sort and datatype declarations and definitions

      case List(Id("declare-sort"), Id(name), Num(digits), attrs*) =>
        val arity = digits.toInt
        val attrs_ = annotation(attrs.toList)
        val con = Con(name, arity)

        state = state.declare(name, arity, attrs_)
        DeclareSort(con, attrs_)

      case List(Id("define-sort"), Id(name), List(params*), body, attrs*) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val arity = params.length
        val con = Con(name, arity)

        val body_ = typ(scope, body)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, arity, attrs_)
        state = state.define(name, params_, body_)
        DefineSort(con, params_, body_, attrs_)

      case List(Id("declare-datatypes"), List(sigs*), List(decls*), attrs*) =>
        val attrs_ = annotation(attrs.toList)

        Error.report("mismatching datatype declarations", sigs, decls):
          require(sigs.length == decls.length)

        // all sorts must be known before any of the constructors
        val names =
          for sig <- sigs.toList
          yield sig match
            case List(Id(name), Num(arity)) =>
              state = state.declare(name, arity.toInt, attrs_)
              name

            case _ =>
              Error.raise("not a datatype signature", sig)

        val datas_ =
          for (name, decl) <- names zip decls.toList
          yield datatype(name, decl)

        DeclareDatatypes(names.map(state.sorts(_)), datas_, attrs_)

      case List(Id("declare-datatype"), Id(name), decl, attrs*) =>
        val attrs_ = annotation(attrs.toList)
        val arity = decl match
          case List(Id("par"), List(params*), _) => params.length
          case _                                 => 0

        state = state.declare(name, arity, attrs_)
        val data_ = datatype(name, decl)
        DeclareDatatypes(List(state.sorts(name)), List(data_), attrs_)

      // polymorphic Alt-Ergo .psmt declarations and definitions

      case List(Id("declare-const"), Id(name), List(Id("par"), List(params*), res, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val formals_ = Nil
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, params_, formals_, res_, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("declare-fun"), Id(name), List(Id("par"), List(params*), List(args*), res, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val args_ = list(args) { typ(scope, _) }
        val formals_ = Expr.vars("x", args_)
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, params_, formals_, res_, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("define-fun"), Id(name), List(Id("par"), List(params*), List(formals*), res, body, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val formals_ = list(formals) { formal(scope, _) }
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)

        val expr_ = expr(scope ++ formals_, body)
        val body_ = state.exprs.check(scope, expr_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, params_, formals_, res_, attrs_)
        state = state.define(name, formals_.length, body_)
        DefineFun(fun, body_, attrs_)

      // monomorphic SMT-LIB declarations and definitions

      case List(Id("declare-const"), Id(name), res, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val formals_ = Nil
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, params_, formals_, res_, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("declare-fun"), Id(name), List(args*), res, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val args_ = list(args) { typ(scope, _) }
        val formals_ = Expr.vars("x", args_)
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, params_, formals_, res_, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("define-fun"), Id(name), List(formals*), res, body, attrs*) =>
        val params_ = Nil
        val scope = Scope.empty

        val formals_ = list(formals) { formal(scope, _) }
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)

        val expr_ = expr(scope ++ formals_, body)
        val body_ = state.exprs.check(scope, expr_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, params_, formals_, res_, attrs_)
        state = state.define(name, formals_.length, body_)
        DefineFun(fun, body_, attrs_)

      // assertions and proof goals

      case List(Id(cmd @ ("assert" | "goal" | "lemma")), List(Id("par"), List(params*), List(Id("!"), phi, attrs*))) =>
        val params_ = list(params) { param(_) }
        assertion(justification(cmd), params_, phi, attrs.toList)

      case List(Id(cmd @ ("assert" | "goal" | "lemma")), List(Id("par"), List(params*), phi, attrs*)) =>
        val params_ = list(params) { param(_) }
        assertion(justification(cmd), params_, phi, attrs.toList)

      case List(Id(cmd @ ("assert" | "goal" | "lemma")), List(Id("!"), phi, attrs*)) =>
        assertion(justification(cmd), Nil, phi, attrs.toList)

      case List(Id(cmd @ ("assert" | "goal" | "lemma")), phi, attrs*) =>
        assertion(justification(cmd), Nil, phi, attrs.toList)

      // procedural fragment

      // global variables, which procedures may modify if they declare so
      case List(Id("declare-var"), Id(name), sort, attrs*) =>
        val typ_ = typ(Scope.empty, sort)
        val attrs_ = annotation(attrs.toList)
        state = state.declare(name, typ_, attrs_)
        state.cmds.declareVar(name)

      case List(Id("declare-proc"), Id(name), List(in*), List(out*), attrs*) =>
        procedure(name, Nil, list(in) { formal(Scope.empty, _) }, list(out) { formal(Scope.empty, _) }, None, attrs.toList)

      case List(Id("define-proc"), Id(name), List(in*), List(out*), body, attrs*) =>
        procedure(name, Nil, list(in) { formal(Scope.empty, _) }, list(out) { formal(Scope.empty, _) }, Some(body), attrs.toList)

      case List(Id("declare-proc"), Id(name), List(Id("par"), List(params*), List(in*), List(out*), attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)
        procedure(name, params_, list(in) { formal(scope, _) }, list(out) { formal(scope, _) }, None, attrs.toList)

      case List(Id("define-proc"), Id(name), List(Id("par"), List(params*), List(in*), List(out*), body, attrs*)) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)
        procedure(name, params_, list(in) { formal(scope, _) }, list(out) { formal(scope, _) }, Some(body), attrs.toList)

      // the commands of SV-LIB (see svlib.Parser), e.g. in printed output that is parsed again
      case List(Id("annotate-tag"), Id(tag), attrs*) =>
        annotate(tag, attrs.toList)

      case List(Id("verify-call"), Id(name), List(args*)) =>
        verifyCall(name, args.toList)

      case _ =>
        Error.raise("not a command", Parser.head(from))

  // procedures are declared together with their contract before the body is resolved, which may call them recursively;
  // they may read all global variables, which the formal parameters shadow,
  // and the inputs and the global variables that are not modified must not be assigned
  def procedure(name: Name, params: List[Param], in: List[Var], out: List[Var], body: Option[Any], attrs: List[Any]): Cmd =
    val globals = state.globals
    val scope = Scope(params) ++ globals ++ in ++ out
    val attrs_ = contract(scope, attrs)

    for tag <- attrs_.tags
    do record(tag, Tagged(scope, Some(scope), attrs_.tags.headOption, (globals ++ in).map(_.name).toSet))

    val mod = attrs_.modifies
    val nonglobal = mod.filterNot(globals.contains)
    Error.report("modifies clause of procedure lists variables that are not global", name, nonglobal):
      require(nonglobal.isEmpty)

    state = state.declare(name, params, in, out, attrs_)

    body match
      case None =>
        state.cmds.declareProc(name)

      case Some(body) =>
        val fixed = in.toSet ++ (globals.toSet -- mod)
        val body_ = state.progs.check(scope, fixed, mod.toSet, prog(scope, body))
        state = state.define(name, body_)
        state.cmds.defineProc(name)

  // the annotations of an annotate-tag command of SV-LIB, resolved like the contract of the first statement with
  // the tag, as if written there; the SV-LIB frontend resolves them by their kind (see svlib.Parser)
  def annotate(tag: Name, from: List[Any]): Cmd =
    Error.report("unknown tag", tag):
      require(tags.contains(tag))

    linked(tag, contract(tags(tag).head.scope, from))

  // the variables of the annotations `attrs` of `tag` must be in scope at every statement with the tag
  def linked(tag: Name, attrs: Attrs): Cmd =
    Error.report("tag in an annotate-tag command", tag):
      require(!attrs.contains("tag"))

    for tagged <- tags(tag).tail do
      val unknown = attrs.free.filterNot(x => tagged.scope.vars.get(x.name) == Some(x))
      Error.report("variables of the annotation are not in scope at every statement with the tag", tag, unknown):
        require(unknown.isEmpty)

    AnnotateTag(tag, attrs)

  // the arguments of a verify-call of SV-LIB are resolved in the scope of the global variables and checked against
  // the signature of the procedure; if it is not declared, e.g. in the output of -verify, where the procedures are
  // replaced by their goals, the arguments are checked on their own
  def verifyCall(name: Name, from: List[Any]): Cmd =
    val scope = Scope(Nil, state.globals)
    val args = list(from) { expr(scope, _) }

    if state.procs.contains(name) then
      val Proc(_, _, _, out) = state.procs(name)
      val res = Expr.vars("r", out.types).fresh
      val mod = state.procattrs(name).modifies.toSet
      state.progs.check(scope ++ res, Set(), mod, Call(name, args, res)) match
        case Call(_, args_, _) => VerifyCall(name, args_)
        case prog              => Error.raise("not a call", prog)
    else
      VerifyCall(name, args.map(arg => state.exprs.check(scope, arg, arg.typ)))

  // attributes whose arguments are resolved: formulas for contracts, invariants and location invariants (SV-LIB),
  // integers for termination measures, lists of variables for modifies, and names for tags (SV-LIB)
  def contract(scope: Scope, from: List[Any]): Attrs =
    val attrs_ =
      for (kw, arg) <- Parser.annotations(from)
      yield (kw, arg) match
        case ("requires" | "ensures" | "invariant" | "check-true" | "assumes" | "commits", Some(phi)) =>
          kw -> Some(state.exprs.check(scope, expr(scope, phi), Sort.bool))

        case ("decreases", Some(arg)) =>
          kw -> Some(state.exprs.check(scope, expr(scope, arg), Sort.int))

        case ("modifies", Some(List(xs*))) =>
          kw -> Some(list(xs) { variable(scope, _) })

        // the tags of SV-LIB, e.g. in printed output that is parsed again
        case ("tag", Some(Id(tag))) =>
          val tag_ : Name = tag
          kw -> Some(tag_)

        case _ =>
          kw -> arg

    Attrs(attrs_)

  def variable(scope: Scope, from: Any): Var =
    from match
      case Id(name) if scope.vars.contains(name) =>
        scope.vars(name)

      case _ =>
        Error.raise("unknown variable", from)

  def variables(scope: Scope, from: Any): List[Var] =
    from match
      case List(xs*) => list(xs) { variable(scope, _) }
      case _         => Error.raise("not a list of variables", from)

  def assignments(scope: Scope, from: Seq[Any]): (List[Var], List[Expr]) =
    val pairs =
      list(from):
        case List(x, arg) => (variable(scope, x), expr(scope, arg))
        case from         => Error.raise("not an assignment", from)
    pairs.unzip

  // programs as written by the printer, the expressions are type checked together with the whole body
  def prog(scope: Scope, from: Any): Prog =
    from match
      case List(Id("break"))    => Break
      case List(Id("continue")) => Continue
      case List(Id("return"))   => Return
      case List(Id("abort"))    => Spec(Nil, False, True)

      case List(Id("assume"), phi) =>
        Spec.assume(expr(scope, phi))

      case List(Id("assert"), phi) =>
        Spec.assert(expr(scope, phi))

      case List(Id("havoc"), xs*) =>
        Spec.havoc(list(xs) { variable(scope, _) })

      case List(Id("spec"), xs, pre, post) =>
        Spec(variables(scope, xs), expr(scope, pre), expr(scope, post))

      case List(Id("assign"), pairs*) =>
        val (lhs, rhs) = assignments(scope, pairs)
        state.progs.assign(lhs, rhs)

      case List(Id("call"), Id(name), List(args*), res) =>
        state.progs.call(name, list(args) { expr(scope, _) }, variables(scope, res))

      case List(Id("block"), List(Id("locals"), locals*), progs*) =>
        val locals_ = list(locals) { formal(scope, _) }
        val scope_ = scope ++ locals_
        state.progs.block(locals_, list(progs) { prog(scope_, _) })

      case List(Id("choose"), progs*) =>
        Choice(list(progs) { prog(scope, _) })

      case List(Id("if"), test, left, right) =>
        state.progs.if_(expr(scope, test), prog(scope, left), prog(scope, right))

      case List(Id("while"), test, body, attrs*) =>
        val attrs_ = contract(scope, attrs.toList)
        for tag <- attrs_.tags do record(tag, Tagged(scope, None, None, Set()))
        state.progs.while_(expr(scope, test), prog(scope, body), attrs_)

      case List(Id("iter"), body, attrs*) =>
        state.progs.iter(prog(scope, body), contract(scope, attrs.toList))

      // the time is bound on Real
      case List(Id("ode"), Id(time), List(pairs*), dom, attrs*) =>
        val time_ = Var(time, Sort.real)
        val scope_ = scope ++ List(time_)
        val (xs, rhs) = assignments(scope_, pairs)
        state.progs.ode(time_, xs, rhs, expr(scope_, dom), contract(scope_, attrs.toList))

      case List(Id("par"), calls*) =>
        val calls_ =
          list(calls):
            case from =>
              prog(scope, from) match
                case call: Call => call
                case prog_      => Error.raise("parallel composition of statements that are not calls", prog_)
        state.progs.par(calls_)

      case _ =>
        Error.raise("not a program", Parser.head(from))

  // the sort `name` must have been declared already as it may occur recursively
  def datatype(name: Name, decl: Any): Datatype =
    val (params_, constrs) =
      decl match
        case List(Id("par"), List(params*), List(constrs*)) =>
          (list(params) { param(_) }, constrs.toList)

        case List(constrs*) =>
          (Nil, constrs.toList)

        case _ =>
          Error.raise("not a datatype declaration", decl)

    val con = state.sorts(name)
    val scope = Scope(params_)
    val sort_ = Sort(con, params_)

    Error.report("wrong number of type parameters", name, con.arity, params_):
      require(con.arity == params_.length)

    val constrs_ =
      for constr <- constrs
      yield
        val (name_, sels) =
          constr match
            case List(Id(name_), sels*) => (name_, sels.toList)
            case Id(name_)              => (name_, Nil)
            case _                      => Error.raise("not a constructor", constr)

        val sels_ =
          for sel <- sels
          yield sel match
            case List(Id(sel), res) =>
              Fun(sel, params_, Expr.vars("x", List(sort_)), typ(scope, res))

            case _ =>
              Error.raise("not a selector", sel)

        val formals_ = Expr.vars("x", sels_.map(_.res))
        (Fun(name_, params_, formals_, sort_), sels_)

    val data_ = Datatype(params_, constrs_)
    state = state.declare(data_).define(name, data_)
    data_

  // goals and lemmas are not part of SMT-LIB, they are written like assertions with their own command
  def justification(cmd: String): Justify =
    cmd match
      case "assert" => Axiom
      case "goal"   => Goal
      case "lemma"  => Lemma
      case _        => Error.raise("not an assertion command", cmd)

  // models are interpreted in the current state, which is not changed:
  // functions that are not declared yet, and the declarations in the model, are local to the model
  def model(from: Any): Model =
    val items =
      from match
        case List(Id("model"), items*) => items.toList
        case List(items*)              => items.toList
        case _                         => Error.raise("invalid model", from)

    val saved = state
    try Model(items map definition)
    finally state = saved

  def definition(from: Any): Decl =
    from match
      // elements of uninterpreted sorts (z3)
      case List(Id("declare-fun"), _*) =>
        cmd(from) match
          case decl: DeclareFun => decl
          case _                => Error.raise("invalid declaration in model", from)

      // the formal parameters are renamed to x$0, x$1, ..., since the names of the solver,
      // e.g. x!0 of z3, are not valid in other languages
      case List(Id("define-fun"), Id(name), List(formals*), res, body) =>
        val formals_ = list(formals) { formal(Scope.empty, _) }
        val res_ = typ(Scope.empty, res)
        val renamed = Expr.vars("x", formals_.types)
        val fun = Fun(name, Nil, renamed, res_)

        if !state.funs.contains((name, formals_.length))
        then state = state.declare(name, Nil, renamed, res_, Attrs.empty)

        val expr_ = expr(Scope(Nil, formals_), body)
        val body_ = state.exprs.check(Scope.empty, expr_, res_)
        DefineFun(fun, Subst.from(formals_, renamed)(body_), Attrs.empty)

      // cardinality constraints of uninterpreted sorts (z3)
      case phi =>
        assertion(Axiom, Nil, phi, Nil)

  def assertion(justify: Justify, params: List[Param], phi: Any, attrs: List[Any]) =
    val scope = Scope(params)
    val expr_ = expr(scope, phi)
    val phi_ = state.exprs.check(scope, expr_, Sort.bool)
    val attrs_ = annotation(attrs)
    Assert(justify, params, phi_, attrs_)

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
        state.types.sort(name)

      case List(Id(name), args*) if state.sorts contains name =>
        val args_ = list(args) { typ(scope, _) }
        state.types.sort(name, args_)

      case List(Id("_"), Id("BitVec"), Num(digits)) if BigInt(digits) > 0 =>
        BitVec(digits.toInt)

      // function types of SMT-LIB 2.7, (-> A B C) of two arguments, not curried (see Arrow)
      case List(Id("->"), args*) if args.length >= 2 =>
        val args_ = list(args) { typ(scope, _) }
        val name = Arrow.con(args_.length - 1).name
        Error.report("function type not declared", from):
          require(state.sorts contains name)
        state.types.sort(name, args_)

      case _ =>
        Error.raise("not a type", from)

  // the types are instantiated with fresh parameters, which are resolved by Type.check
  def app(name: Name, args: List[Expr]): Expr =
    val fun = state.funs((name, args.length))

    val su = Subst.fresh(fun.params)
    val inst_ = su(fun.args)
    val typ_ = su(fun.res)
    App(fun, inst_, typ_, args)

  // the application of the function on bitvectors `name`, where the widths of the arguments must be known,
  // functions on bitvectors of the same width also take it from another argument, e.g. of a polymorphic function
  def bitvec(scope: Scope, name: String, indices: List[Int], args: List[Any], from: Any): Expr =
    val args_ = list(args) { expr(scope, _) }
    val known = args_.collect { case arg if arg.typ.isInstanceOf[BitVec] => arg.typ.asInstanceOf[BitVec].n }

    val widths =
      for arg <- args_
      yield arg.typ match
        case BitVec(n)                                   => n
        case _ if name != "concat" && known.nonEmpty     => known.head
        case _                                           => Error.raise("unknown width of bitvector", from)

    BitVecs.fun(name, indices, widths) match
      case Some(fun) => App(fun, fun.args, fun.res, args_)
      case None      => Error.raise("invalid application of bitvector function", from, widths)

  // the application of a function value to `args`, of the arity of its type if that is known already
  def apply(f: Expr, args: List[Expr], from: Any): Expr =
    f.typ match
      case Arrow(params, _) if params.length < args.length =>
        val (first, rest) = args.splitAt(params.length)
        apply(apply(f, first, from), rest, from)

      case _ =>
        val name = Name("apply", Some(args.length))
        Error.report("function type not declared", from):
          require(state.funs contains (name, args.length + 1))
        app(name, f :: args)

  // applications of binary functions to more than two arguments
  def nary(name: Name, args: List[Expr]): Expr =
    def and(phis: List[Expr]) =
      phis.reduceLeft((phi, psi) => app("and", List(phi, psi)))

    name match
      case Name("=>", None) =>
        args.reduceRight((phi, psi) => app(name, List(phi, psi)))

      case Name("=" | "<" | "<=" | ">" | ">=", None) =>
        and(for (a, b) <- args zip args.tail yield app(name, List(a, b)))

      case _ =>
        args.reduceLeft((a, b) => app(name, List(a, b)))

  def expr(scope: Scope, from: Any): Expr =
    from match
      case Num(digits) =>
        Lit(BigInt(digits), Sort.int)

      case Dec(digits) =>
        Lit(Rational.decimal(digits), Sort.real)

      case Str(text) =>
        Lit(text, Sort.string)

      // bitvector literals, whose width is that of the digits
      case Bin(digits) =>
        BitVecs.lit(BigInt(digits, 2), digits.length)

      case Hex(digits) =>
        BitVecs.lit(BigInt(digits, 16), 4 * digits.length)

      case List(Id("_"), Id(name), Num(width)) if name.startsWith("bv") && name.drop(2).forall(_.isDigit) && name.length > 2 =>
        BitVecs.lit(BigInt(name.drop(2)), width.toInt)

      // functions on bitvectors, instantiated for the widths of their arguments
      case List(Id(name), args*) if BitVecs.names.contains(name) =>
        bitvec(scope, name, Nil, args.toList, from)

      // the conversion of an integer to a bitvector, whose width is the index
      case List(List(Id("_"), Id("int2bv"), Num(width)), arg) if BigInt(width) > 0 =>
        val fun = BitVecs.int2bv(width.toInt)
        App(fun, fun.args, fun.res, List(expr(scope, arg)))

      case List(List(Id("_"), Id(name), indices*), args*) if BitVecs.indexed.contains(name) =>
        val indices_ =
          for case Num(digits) <- indices.toList
          yield digits.toInt
        bitvec(scope, name, indices_, args.toList, from)

      // rational literals, as printed by the printer and by solvers in models
      case List(Id("/"), Dec(num), Dec(den)) if !Rational.decimal(den).isZero =>
        Lit(Rational.decimal(num) / Rational.decimal(den), Sort.real)

      // annotations inside terms are parsed but discarded, e.g. (! e :weight 0) in models of z3
      case List(Id("!"), arg, attrs*) =>
        Parser.annotations(attrs.toList)
        expr(scope, arg)

      // negative literals, as printed by the printer
      case List(Id("-"), Num(digits)) =>
        Lit(-BigInt(digits), Sort.int)

      case List(Id("-"), Dec(digits)) =>
        Lit(-Rational.decimal(digits), Sort.real)

      case Id(name) if scope.vars.contains(name) =>
        scope.vars(name)

      // constant arrays
      case List(List(Id("as"), Id("const"), sort), arg) =>
        typ(scope, sort) match
          case typ_ @ Sort(Con.array, List(dom, ran)) =>
            val fun = state.funs(("const", 1))
            App(fun, List(ran), typ_, List(expr(scope, arg)))

          case typ_ =>
            Error.raise("constant array must have array type", from, typ_)

      // abstract values in models start with @ and are declared on first use (cvc5)
      case List(Id("as"), Id(name), sort) if name.startsWith("@") && !state.funs.contains((name, 0)) =>
        val typ_ = typ(scope, sort)
        state = state.declare(name, Nil, Nil, typ_, Attrs.empty)
        As(app(name, Nil), typ_)

      // the annotation is kept, its type is checked against that of the expression by type checking
      case List(Id("as"), arg, sort) =>
        As(expr(scope, arg), typ(scope, sort))

      // not part of SMT-LIB, the value at the entry of the procedure, and derivatives
      case List(Id("old"), arg) =>
        state.exprs.old(expr(scope, arg))

      case List(Id("diff"), xs, arg) =>
        state.exprs.diff(variables(scope, xs), expr(scope, arg))

      // testers of constructors
      case List(List(Id("_"), Id("is"), Id(name)), arg) =>
        val constrs = state.constrs

        Error.report("unknown constructor", name):
          require(constrs contains name)

        Is(expr(scope, arg), constrs(name))

      case Id(name) if state.funs.contains((name, 0)) =>
        app(name, Nil)

      // distinct is n-ary and not declared as a function
      case List(Id("distinct"), args*) if args.length >= 2 =>
        val args_ = list(args) { expr(scope, _) }
        Distinct(args_)

      case List(Id(name), args*) if state.funs.contains((name, args.length)) =>
        val args_ = list(args) { expr(scope, _) }
        app(name, args_)

      case List(Id(name), args*) if args.length > 2 && state.funs.contains((name, 2)) =>
        val args_ = list(args) { expr(scope, _) }
        nary(name, args_)

      case List(Id("forall"), List(bound*), body) =>
        val bound_ = list(bound) { formal(scope, _) }
        val scope_ = scope ++ bound_
        val body_ = expr(scope_, body)
        All(bound_, body_)

      case List(Id("exists"), List(bound*), body) =>
        val bound_ = list(bound) { formal(scope, _) }
        val scope_ = scope ++ bound_
        val body_ = expr(scope_, body)
        Ex(bound_, body_)

      // applications of function values of SMT-LIB 2.7, (@ f a b), which is left-associative:
      // a function of fewer arguments is applied to the first ones, and its result to the rest
      case List(Id("@"), f, args*) if args.nonEmpty =>
        val f_ = expr(scope, f)
        val args_ = list(args) { expr(scope, _) }
        apply(f_, args_, from)

      // an array of a single index, since those of several indices are not curried in SMT-LIB (unlike Boogie),
      // and not a function (see Lam), since solvers support lambdas of array type only
      case List(Id("lambda"), List(bound*), body) =>
        val bound_ = list(bound) { formal(scope, _) }
        Error.report("lambda of several variables not supported", from):
          require(bound_.length == 1)
        val scope_ = scope ++ bound_
        val body_ = expr(scope_, body)
        state.exprs.lams(bound_, body_)

      // not part of SMT-LIB, the choice of a result whose guard holds, (eps (guard result) ...)
      case List(Id("eps"), cases*) =>
        val updates =
          list(cases):
            case List(cond, rhs) => Upd(expr(scope, cond), expr(scope, rhs))
            case from            => Error.raise("not a case of a choice", from)
        Eps(updates)

      // not part of SMT-LIB, the combinators of trace equation systems, whose dependencies are bound like let,
      // (trace (x init) ((y Y) ...) update), (map ((y Y) ...) update), (all ((y Y) ...) body)
      case List(Id("trace"), List(Id(acc), init), List(bindings*), update) =>
        val init_ = expr(scope, init)
        val (bound_, deps_) = leteqs(scope, bindings)
        state.exprs.trace(init_, deps_, acc, bound_.map(_.name)): (acc_, bound__) =>
          expr(scope ++ (acc_ :: bound__), update)

      case List(Id("map"), List(bindings*), update) =>
        val (bound_, deps_) = leteqs(scope, bindings)
        state.exprs.map(deps_, bound_.map(_.name)): bound__ =>
          expr(scope ++ bound__, update)

      case List(Id("invs"), List(bindings*), body) =>
        val (bound_, deps_) = leteqs(scope, bindings)
        state.exprs.all(deps_, bound_.map(_.name)): bound__ =>
          expr(scope ++ bound__, body)

      // bindings are parallel, all bound expressions are parsed in the outer scope,
      // the bound variables have the types of their expressions, which are resolved by Type.check
      case List(Id("let"), List(bindings*), body) =>
        val (bound_, args_) = leteqs(scope, bindings)
        val body_ = expr(scope ++ bound_, body)
        Let(bound_, args_, body_)

      case _ =>
        Error.raise("not an expression", from)

  def leteqs(scope: Scope, from: Seq[Any]): (List[Var], List[Expr]) =
    val eqs = list(from) { leteq(scope, _) }
    eqs.unzip

  def leteq(scope: Scope, from: Any): (Var, Expr) =
    from match
      case List(Id(name), arg) =>
        val arg_ = expr(scope, arg)
        (Var(name, arg_.typ), arg_)

      case _ =>
        Error.raise("not a let binding", from)

