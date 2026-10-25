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

  // the polymorphic form of a declaration, definition, or assertion, (cmd name (par (a ...) args ...)) and
  // (cmd (par (a ...) phi attrs ...)), as the monomorphic form with the type parameters a ..., none for that form
  def polymorphic(from: Any): (List[Any], Any) =
    from match
      case List(cmd @ Id("declare-const" | "declare-fun" | "define-fun" | "declare-proc" | "define-proc"), name, List(Id("par"), List(params*), args*)) =>
        (params.toList, List(cmd, name) ++ args)

      case List(cmd @ Id("assert" | "goal" | "lemma"), List(Id("par"), List(params*), args*)) =>
        (params.toList, List(cmd) ++ args)

      case _ =>
        (Nil, from)

  // a statement of SV-LIB with a tag: the scope of its properties, which is that of the signature for the body of a
  // procedure, whose contract cannot refer to the local variables, and the enclosing procedure, whose signature gives
  // the variables that (at x tag) may refer to
  case class Tagged(scope: Scope, proc: Name)

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
    val (params, from_) = Parser.polymorphic(from)

    from_ match
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

      // declarations and definitions, monomorphic as in SMT-LIB or polymorphic as in Alt-Ergo's .psmt, (par (a ...)
      // ...), whose type parameters `params` are those of the polymorphic form (see Parser.polymorphic)

      case List(Id("declare-const"), Id(name), res, attrs*) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val formals_ = Nil
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)
        val attrs_ = annotation(attrs.toList)

        state = state.declare(name, params_, formals_, res_, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("declare-fun"), Id(name), List(args*), res, attrs*) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val args_ = list(args) { typ(scope, _) }
        val formals_ = Expr.vars("x", args_)
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)
        val attrs_ = implementation(name, scope ++ formals_, List(res_), annotation(attrs.toList))

        state = state.declare(name, params_, formals_, res_, attrs_)
        DeclareFun(fun, attrs_)

      case List(Id("define-fun"), Id(name), List(formals*), res, body, attrs*) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)

        val formals_ = list(formals) { formal(scope, _) }
        val res_ = typ(scope, res)
        val fun = Fun(name, params_, formals_, res_)

        val expr_ = expr(scope ++ formals_, body)
        val body_ = state.exprs.check(scope, expr_, res_)
        val attrs_ = implementation(name, scope ++ formals_, List(res_), annotation(attrs.toList))

        state = state.declare(name, params_, formals_, res_, attrs_)
        state = state.define(name, formals_.length, body_)
        DefineFun(fun, body_, attrs_)

      // assertions and proof goals

      case List(Id(cmd @ ("assert" | "goal" | "lemma")), List(Id("!"), phi, attrs*)) =>
        assertion(justification(cmd), list(params) { param(_) }, phi, attrs.toList)

      case List(Id(cmd @ ("assert" | "goal" | "lemma")), phi, attrs*) =>
        assertion(justification(cmd), list(params) { param(_) }, phi, attrs.toList)

      // procedural fragment, the syntax of SV-LIB (see the comment on procedure)

      // global variables, which procedures may modify
      case List(Id("declare-var"), Id(name), sort, attrs*) =>
        val typ_ = typ(Scope.empty, sort)
        val attrs_ = annotation(attrs.toList)
        state = state.declare(name, typ_, attrs_)
        state.cmds.declareVar(name)

      // not part of SV-LIB: procedures without body, whose contract and modifies clause are attributes, and
      // polymorphic procedures
      case List(Id("declare-proc"), Id(name), List(in*), List(out*), attrs*) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)
        declaration(name, params_, list(in) { formal(scope, _) }, list(out) { formal(scope, _) }, attrs.toList)

      case List(Id("define-proc"), Id(name), List(in*), List(out*), List(locals*), body) =>
        val params_ = list(params) { param(_) }
        val scope = Scope(params_)
        val in_ = list(in) { formal(scope, _) }
        val out_ = list(out) { formal(scope, _) }
        val locals_ = list(locals) { formal(scope, _) }
        procedure(name, params_, in_, out_, locals_, body)

      case List(Id("define-procs-rec"), _*) =>
        Error.raise("not supported", "define-procs-rec")

      case List(Id("annotate-tag"), Id(tag), attrs*) =>
        annotate(tag, attrs.toList)

      case List(Id("verify-call"), Id(name), List(args*)) =>
        verifyCall(name, args.toList)

      // witnesses are not produced, the answer is unsupported (see Sink)
      case List(Id("get-witness")) =>
        GetWitness

      case List(Id("select-trace"), _*) =>
        Error.raise("not supported", "select-trace")

      case _ =>
        Error.raise("not a command", Parser.head(from))

  // a procedure without body is declared with its contract, which may refer to its type parameters, the global
  // variables, which the formal parameters shadow, and its formal parameters; the global variables that it modifies
  // are listed, since there is no body to infer them from
  def declaration(name: Name, params: List[Param], in: List[Var], out: List[Var], attrs: List[Any]): Cmd =
    val globals = state.globals
    val scope = Scope(params) ++ globals ++ in ++ out
    val attrs_ = implementation(name, Scope(params) ++ in, out.types, contract(scope, attrs))
    state.progs.modifies(name, attrs_.modifies)

    state = state.declare(name, params, in, out, attrs_)
    state.cmds.declareProc(name)

  // programs in the syntax of SV-LIB: procedures with local variables, whose properties are attributes of loops and
  // of procedure bodies, written inline as (! s attrs) or linked by annotate-tag commands to the statements with the
  // tag; the variables of a property are resolved in the scope of the tagged statement, its functions in the state at
  // the command, which is why annotate-tag commands are resolved here but attached to the statements only by the
  // transforms (see State.annotated); the global variables that procedures modify are inferred, unless the body lists
  // them as :modifies, loops have no modifies clause unless they list one;
  // not part of SV-LIB: blocks with local variables, assert, spec, abort, iter, ode, par, polymorphic procedures, and
  // procedures without body (see declaration);
  // not supported: define-procs-rec, labels and gotos, tags on statements other than loops, procedure bodies and
  // sequences, the properties recurring, not-recurring and decreases-lex, witnesses (get-witness answers unsupported)
  // and traces
  //
  // the signature is declared before the body is resolved, which may call the procedure recursively;
  // the body may read all global variables, and the inputs and the other global variables must not be assigned
  // (see Type.check); the local variables are those of the block of the body
  def procedure(name: Name, params: List[Param], in: List[Var], out: List[Var], locals: List[Var], body: Any): Cmd =
    val globals = state.globals
    val formals = in ++ out ++ locals

    Error.report("duplicate parameters or local variables of procedure", name, formals):
      require(formals.distinctBy(_.name) == formals)

    val outer = Scope(params) ++ globals ++ in ++ out
    val scope = outer ++ locals

    // the tags of the body are declared with the signature, (at x tag) of the statements inside refers to them
    val (inner, attrs) = annotated(body)
    val tags_ = Attrs(tagsOf(attrs).map("tag" -> Some(_)))
    state = state.declare(name, params, in, out, tags_)

    val tagged = Tagged(outer, name)
    for tag <- tagsOf(attrs) do record(tag, tagged)

    val progs =
      stmt(scope, name, inner) match
        case Block(Nil, progs, attrs) if attrs.isEmpty => progs
        case prog                                       => List(prog)

    // location invariants of the body hold at the entry
    val attrs_ = properties(tagged, true, attrs)
    val body_ = Block(locals, attrs_.checks.map(Spec.assert) ++ progs)

    state.progs.modifies(name, attrs_.modifies)

    val attrs__ = implementation(name, Scope(params) ++ in, out.types, inferred(name, Attrs(attrs_.attrs.filterNot(_._1 == "check-true")), body_))

    // the modifies clause is recorded before the body is checked, which resolves the calls with the modifies clauses
    // of their procedures (see Call), also the recursive ones
    state = state.copy(procattrs = state.procattrs + (name -> attrs__))
    val checked = state.progs.body(outer, in, attrs__.modifies, body_)
    state = state.define(name, checked)
    DefineProc(state.procs(name), checked, attrs__)

  // the properties of the body `prog` of procedure `name` with its modifies clause, unless it lists one already
  def inferred(name: Name, attrs: Attrs, prog: Prog): Attrs =
    if attrs.contains("modifies") then attrs else attrs ++ modifies(name, prog)

  // the global variables that the body `prog` of procedure `name` assigns, directly or by the procedures that it calls,
  // whose modifies clauses are known, as its modifies clause; a recursive call modifies the global variables of this
  // clause, hence it adds none, and as mutual recursion is not supported (define-procs-rec), this is the fixpoint;
  // the calls of `prog` are not resolved yet, they modify no global variables (see Call), and .mod has the assigned
  // local variables and results as well
  def modifies(name: Name, prog: Prog): Attrs =
    val called = (prog.calls - name).toList.flatMap(state.procattrs.get(_).toList.flatMap(_.modifies))
    val mod = ((prog.mod ++ called) intersect state.globals.toSet).toList.sortBy(_.name.toString)
    if mod.isEmpty
    then Attrs.empty
    else Attrs(List("modifies" -> Some(mod)))

  // the statement of an annotation (! s attrs) with its attributes, where nested annotations are merged,
  // (! (! s a) b) is (! s a b), and a statement without annotation has none
  def annotated(from: Any): (Any, List[Any]) =
    from match
      case List(Id("!"), inner, attrs*) =>
        val (inner_, attrs_) = annotated(inner)
        (inner_, attrs_ ++ attrs)

      case _ =>
        (from, Nil)

  def tagsOf(from: List[Any]): List[Name] =
    Parser.annotations(from).collect:
      case ("tag", Some(Id(tag))) =>
        val tag_ : Name = tag
        tag_

  // the statements inside the procedure `proc`
  def stmt(scope: Scope, proc: Name, from: Any): Prog =
    from match
      case List(Id("!"), _*) =>
        val (inner, attrs) = annotated(from)

        inner match
          case List(Id("while"), test, prog) =>
            val tagged = Tagged(scope, proc)
            for tag <- tagsOf(attrs) do record(tag, tagged)
            val prog_ = stmt(scope, proc, prog)
            state.progs.while_(expr(scope, test), prog_, properties(tagged, true, attrs))

          case List(Id("iter"), prog) =>
            val tagged = Tagged(scope, proc)
            for tag <- tagsOf(attrs) do record(tag, tagged)
            val prog_ = stmt(scope, proc, prog)
            state.progs.iter(prog_, properties(tagged, true, attrs))

          // the properties may refer to the time, which is bound on Real
          case List(Id("ode"), Id(time), List(pairs*), dom) =>
            val time_ = Var(time, Sort.real)
            val scope_ = scope ++ List(time_)
            val (xs, rhs) = assignments(scope_, pairs)
            val tagged = Tagged(scope_, proc)
            for tag <- tagsOf(attrs) do record(tag, tagged)
            state.progs.ode(time_, xs, rhs, expr(scope_, dom), properties(tagged, true, attrs))

          // a sequence with tags is a block with its tags and location invariants, which the transforms assert at its
          // beginning (see State.annotated)
          case List(Id("sequence"), progs*) if tagsOf(attrs).nonEmpty =>
            val tagged = Tagged(scope, proc)
            for tag <- tagsOf(attrs) do record(tag, tagged)
            Block(Nil, list(progs) { stmt(scope, proc, _) }, properties(tagged, true, attrs))

          // the core has no attributes on other statements: their location invariants are asserted before them
          // and tags, which annotate-tag commands could refer to later, are rejected
          case _ =>
            for case ("tag", Some(tag)) <- Parser.annotations(attrs) do
              Error.raise("tag on a statement that is neither a loop, the body of a procedure, nor a sequence", tag)

            val attrs_ = properties(Tagged(scope, proc), true, attrs)
            val progs =
              stmt(scope, proc, inner) match
                case Block(Nil, Nil, attrs) if attrs.isEmpty => Nil
                case prog                                     => List(prog)

            attrs_.checks.map(Spec.assert) ++ progs match
              case List(prog) => prog
              case progs_     => Block(Nil, progs_)

      case List(Id("assume"), phi) =>
        Spec.assume(expr(scope, phi))

      case List(Id("assign"), pairs*) =>
        val (lhs, rhs) = assignments(scope, pairs)
        state.progs.assign(lhs, rhs)

      case List(Id("havoc"), xs*) =>
        Spec.havoc(list(xs) { variable(scope, _) })

      case List(Id("sequence"), progs*) =>
        state.progs.block(Nil, list(progs) { stmt(scope, proc, _) })

      case List(Id("choice"), progs*) if progs.nonEmpty =>
        Choice(list(progs) { stmt(scope, proc, _) })

      case List(Id("call"), Id(name), List(args*), List(res*)) =>
        state.progs.call(name, list(args) { expr(scope, _) }, list(res) { variable(scope, _) })

      case List(Id("return")) =>
        Return

      case List(Id("break")) =>
        Break

      case List(Id("continue")) =>
        Continue

      case List(Id("if"), test, left) =>
        state.progs.if_(expr(scope, test), stmt(scope, proc, left), Block(Nil, Nil))

      case List(Id("if"), test, left, right) =>
        state.progs.if_(expr(scope, test), stmt(scope, proc, left), stmt(scope, proc, right))

      case List(Id("while"), test, prog) =>
        val prog_ = stmt(scope, proc, prog)
        state.progs.while_(expr(scope, test), prog_, Attrs.empty)

      case List(Id("label" | "goto"), _*) =>
        Error.raise("not supported", "labels and gotos")

      // not part of SV-LIB

      case List(Id("assert"), phi) =>
        Spec.assert(expr(scope, phi))

      case List(Id("abort")) =>
        Spec(Nil, False, True)

      case List(Id("spec"), xs, pre, post) =>
        Spec(variables(scope, xs), expr(scope, pre), expr(scope, post))

      case List(Id("block"), List(Id("locals"), locals*), progs*) =>
        val locals_ = list(locals) { formal(scope, _) }
        val scope_ = scope ++ locals_
        state.progs.block(locals_, list(progs) { stmt(scope_, proc, _) })

      case List(Id("iter"), prog) =>
        val prog_ = stmt(scope, proc, prog)
        state.progs.iter(prog_, Attrs.empty)

      // the time is bound on Real
      case List(Id("ode"), Id(time), List(pairs*), dom) =>
        val time_ = Var(time, Sort.real)
        val scope_ = scope ++ List(time_)
        val (xs, rhs) = assignments(scope_, pairs)
        state.progs.ode(time_, xs, rhs, expr(scope_, dom), Attrs.empty)

      case List(Id("par"), calls*) =>
        val calls_ =
          list(calls):
            case from =>
              stmt(scope, proc, from) match
                case call: Call => call
                case prog_      => Error.raise("parallel composition of statements that are not calls", prog_)
        state.progs.par(calls_)

      case _ =>
        Error.raise("not a statement", Parser.head(from))

  // the properties of the statement `tagged`, written `inline` as its annotation or in an annotate-tag command, whose
  // values are resolved by their keyword, wherever they are written: formulas for location invariants, invariants and
  // contracts, which are those of the core, integers for termination measures, names for tags, and variables for
  // modifies clauses; other attributes, e.g. :named, are kept
  def properties(tagged: Tagged, inline: Boolean, from: List[Any]): Attrs =
    val scope = tagged.scope

    val attrs_ =
      for (kw, arg) <- Parser.annotations(from)
      yield (kw, arg) match
        case ("tag", Some(Id(tag))) if inline =>
          val tag_ : Name = tag
          kw -> Some(tag_)

        case ("tag", _) =>
          Error.raise("tag in an annotate-tag command", arg.getOrElse(kw))

        // the precondition is evaluated at the entry, where the old values are the current ones (see State.declare)
        case ("requires", Some(phi)) =>
          kw -> Some(Old.elim(Nil, Nil, formula(tagged, scope, phi)))

        // not part of SV-LIB: the assumption and commitment of a procedure (see verify.VCGen)
        case ("check-true" | "invariant" | "ensures" | "assumes" | "commits", Some(phi)) =>
          kw -> Some(formula(tagged, scope, phi))

        case ("decreases", Some(arg)) =>
          kw -> Some(integer(tagged, scope, arg))

        // not part of SV-LIB: the global variables that a procedure or loop modifies, in place of those inferred
        case ("modifies", Some(List(xs*))) =>
          kw -> Some(list(xs) { variable(scope, _) })

        case ("recurring" | "not-recurring" | "decreases-lex", _) =>
          Error.raise("not supported", kw)

        case _ =>
          kw -> arg

    Attrs(attrs_)

  def formula(tagged: Tagged, scope: Scope, from: Any): Expr =
    state.exprs.check(scope, expr(scope, at(tagged, from)), Sort.bool)

  def integer(tagged: Tagged, scope: Scope, from: Any): Expr =
    state.exprs.check(scope, expr(scope, at(tagged, from)), Sort.int)

  // (at x tag) refers to the value of the variable x at the entry of the enclosing procedure, old(x), if `tag` is
  // the tag of its body, which is supported for global variables (see Old.elim) and for inputs, which are never
  // assigned; the values of outputs and locals at the entry, other tags, and final are not supported
  def at(tagged: Tagged, from: Any): Any =
    from match
      case List(Id("at"), Id(x), Id(tag)) =>
        val x_ : Name = x
        val tag_ : Name = tag
        val Proc(_, _, in, _) = state.procs(tagged.proc)

        Error.report("at refers to a tag other than that of the body of the procedure", from):
          require(state.procattrs(tagged.proc).tags.contains(tag_))

        Error.report("at refers to a variable that is neither global nor an input", from):
          require((state.globals ++ in).exists(_.name == x_))

        List(Id("old"), Id(x))

      case List(Id("at" | "final"), _*) =>
        Error.raise("not supported", from)

      case List(args*) =>
        args.toList.map(at(tagged, _))

      case _ =>
        from

  // the annotations of an annotate-tag command, resolved as if written at the first statement with the tag
  def annotate(tag: Name, from: List[Any]): Cmd =
    Error.report("unknown tag", tag):
      require(tags.contains(tag))

    linked(tag, properties(tags(tag).head, false, from))

  // the variables of the annotations `attrs` of `tag` must be in scope at every statement with the tag
  def linked(tag: Name, attrs: Attrs): Cmd =
    Error.report("tag in an annotate-tag command", tag):
      require(!attrs.contains("tag"))

    for tagged <- tags(tag).tail do
      val unknown = attrs.free.filterNot(x => tagged.scope.vars.get(x.name) == Some(x))
      Error.report("variables of the annotation are not in scope at every statement with the tag", tag, unknown):
        require(unknown.isEmpty)

    AnnotateTag(tag, attrs)

  // the arguments of a verify-call are terms over the global variables, checked against the inputs of the procedure,
  // which must be declared
  def verifyCall(name: Name, from: List[Any]): Cmd =
    val scope = Scope(Nil, state.globals)
    VerifyCall(name, state.exprs.arguments(scope, name, list(from) { expr(scope, _) }))

  // the attributes of a procedure without body, whose arguments are resolved: formulas for contracts, integers for
  // termination measures, and lists of variables for modifies
  def contract(scope: Scope, from: List[Any]): Attrs =
    val attrs_ =
      for (kw, arg) <- Parser.annotations(from)
      yield (kw, arg) match
        case ("requires" | "ensures" | "assumes" | "commits", Some(phi)) =>
          kw -> Some(state.exprs.check(scope, expr(scope, phi), Sort.bool))

        case ("decreases", Some(arg)) =>
          kw -> Some(state.exprs.check(scope, expr(scope, arg), Sort.int))

        case ("modifies", Some(List(xs*))) =>
          kw -> Some(list(xs) { variable(scope, _) })

        case _ =>
          kw -> arg

    Attrs(attrs_)

  // the pattern of :implement, by which a function or a procedure names the function that it implements and the
  // positions of its arguments, an application to its inputs in `scope`, of the type of its single result, the result
  // of a function or the output of a procedure, among `results` (see transform.Implement); other attributes unchanged
  def implementation(name: Name, scope: Scope, results: List[Type], attrs: Attrs): Attrs =
    val attrs_ =
      for (kw, arg) <- attrs.attrs
      yield (kw, arg) match
        case ("implement", Some(pattern)) =>
          Error.report("an implementation with :implement pattern has a single result", name.subscripted):
            require(results.length == 1)
          Error.report("the pattern of :implement does not have the result type of the implementation", name.subscripted):
            kw -> Some(state.exprs.check(scope, expr(scope, pattern), results.head))

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

      // not part of SMT-LIB, temporal operators and placeholders, unless they are declared functions, e.g. in SV-LIB
      case List(Id(op), args*) if (Prop.ops.contains(Name(op, None)) || Prop.isPlaceholder(op)) && !state.funs.contains((op, args.length)) =>
        val args_ = list(args) { expr(scope, _) }
        Prop(if Prop.isPlaceholder(op) then op else Name(op, None), args_)

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

      // several accumulators, bound like the dependencies, with one result each, (trace ((x₁ e₁) (x₂ e₂)) ((y Y)) u₁ u₂)
      case List(Id("trace"), List(accs*), List(bindings*), results*) =>
        val (accs_, inits_) = leteqs(scope, accs)
        val (bound_, deps_) = leteqs(scope, bindings)
        Error.report("mismatching accumulators and results of a trace", from):
          require(accs_.length == results.length)
        state.exprs.trace(inits_, deps_, accs_.map(_.name), bound_.map(_.name)): (accs__, bound__) =>
          results.toList.map(expr(scope ++ (accs__ ++ bound__), _))

      // the component i of the last value and the history of a trace of several accumulators (see core.Component)
      case List(List(Id("_"), Id("current"), Num(index)), trace) =>
        Component(expr(scope, trace), index.toInt)

      case List(List(Id("_"), Id("butlast"), Num(index)), trace) =>
        History(expr(scope, trace), index.toInt)

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

