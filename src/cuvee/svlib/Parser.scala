package cuvee.svlib

import util.Name
import cuvee.Error
import cuvee.sexpr.Id
import cuvee.core._
import cuvee.core.Attrs

object Parser:
  // what a property annotates: a loop, the body of a procedure, or another statement, which has no attributes
  // in the core, such that only location invariants (check-true) are allowed, as assertions before it
  enum Kind:
    case Loop, Body, Statement

// SV-LIB scripts: SMT-LIB with global variables, procedures with local variables, and the query verify-call (see Cmd),
// whose properties are attributes of loops and of procedure bodies, written inline as (! s attrs) or linked by
// annotate-tag commands to the statements with the tag; the variables of a property are resolved in the scope of
// the tagged statement, its functions in the state at the command, which is why annotate-tag commands are resolved
// here but attached to the statements only by the transforms (see State.annotated); the global variables that
// procedures and loops modify are inferred;
// not supported: define-procs-rec, labels and gotos, tags on other statements, the properties recurring,
// not-recurring and decreases-lex, witnesses and traces
class Parser(init: State) extends cuvee.smtlib.Parser(init):
  import cuvee.smtlib.Parser.annotations
  import cuvee.smtlib.Parser.Tagged
  import Parser.Kind

  override def cmd(from: Any): Cmd =
    from match
      case List(Id("define-proc"), Id(name), List(in*), List(out*), List(locals*), body) =>
        val in_ = list(in) { formal(Scope.empty, _) }
        val out_ = list(out) { formal(Scope.empty, _) }
        val locals_ = list(locals) { formal(Scope.empty, _) }
        procedure(name, in_, out_, locals_, body)

      case List(Id("define-procs-rec"), _*) =>
        Error.raise("not supported", "define-procs-rec")

      case List(Id("get-witness")) =>
        Error.raise("not supported", "get-witness")

      case List(Id("select-trace"), _*) =>
        Error.raise("not supported", "select-trace")

      case _ =>
        super.cmd(from)

  // the signature is declared before the body is resolved, which may call the procedure recursively;
  // the body may read all global variables, and modifies those that it assigns or that its calls modify,
  // the inputs and the other global variables must not be assigned (see Type.check);
  // the local variables are those of the block of the body
  def procedure(name: Name, in: List[Var], out: List[Var], locals: List[Var], body: Any): Cmd =
    val globals = state.globals
    val formals = in ++ out ++ locals

    Error.report("duplicate parameters or local variables of procedure", name, formals):
      require(formals.distinctBy(_.name) == formals)

    val outer = Scope(Nil, globals) ++ in ++ out
    val scope = outer ++ locals
    val entry = (globals ++ in).map(_.name).toSet

    state = state.declare(name, Nil, in, out, Attrs.empty)

    val (inner, attrs) = annotated(body)
    val tagged = Tagged(scope, Some(outer), tagsOf(attrs).headOption, entry)
    for tag <- tagsOf(attrs) do record(tag, tagged)

    val progs =
      stmt(scope, tagged, inner) match
        case Block(Nil, progs) => progs
        case prog              => List(prog)

    // location invariants of the body hold at the entry
    val attrs_ = properties(tagged, Kind.Body, true, attrs)
    val body_ = Block(locals, attrs_.checks.map(Spec.assert) ++ progs)
    val mod = modifies(body_)
    val attrs__ = Attrs(attrs_.attrs.filterNot(_._1 == "check-true")) ++ mod

    val fixed = in.toSet ++ (globals.toSet -- mod.modifies)
    val checked = state.progs.check(outer, fixed, mod.modifies.toSet, body_)
    state = state.copy(procattrs = state.procattrs + (name -> attrs__)).define(name, checked)
    DefineProc(state.procs(name), checked, attrs__)

  // the global variables that `prog` assigns, directly or by calls (see Par.modifies), as its modifies clause
  def modifies(prog: Prog): Attrs =
    val mod = (Par.modifies(state, prog) intersect state.globals.toSet).toList.sortBy(_.name.toString)
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
    annotations(from).collect:
      case ("tag", Some(Id(tag))) =>
        val tag_ : Name = tag
        tag_

  // the statements inside the procedure whose body is `body`
  def stmt(scope: Scope, body: Tagged, from: Any): Prog =
    from match
      case List(Id("!"), _*) =>
        val (inner, attrs) = annotated(from)

        inner match
          case List(Id("while"), test, prog) =>
            val tagged = Tagged(scope, None, body.body, body.entry)
            for tag <- tagsOf(attrs) do record(tag, tagged)
            val prog_ = stmt(scope, body, prog)
            val attrs_ = properties(tagged, Kind.Loop, true, attrs) ++ modifies(prog_)
            state.progs.while_(expr(scope, test), prog_, attrs_)

          // the core has no attributes on other statements: their location invariants are asserted before them
          // and tags, which annotate-tag commands could refer to later, are rejected (see properties)
          case _ =>
            val tagged = Tagged(scope, None, body.body, body.entry)
            val attrs_ = properties(tagged, Kind.Statement, true, attrs)
            val progs =
              stmt(scope, body, inner) match
                case Block(Nil, Nil) => Nil
                case prog            => List(prog)

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
        state.progs.block(Nil, list(progs) { stmt(scope, body, _) })

      case List(Id("choice"), progs*) if progs.nonEmpty =>
        Choice(list(progs) { stmt(scope, body, _) })

      case List(Id("call"), Id(name), List(args*), List(res*)) =>
        state.progs.call(name, list(args) { expr(scope, _) }, list(res) { variable(scope, _) })

      case List(Id("return")) =>
        Return

      case List(Id("break")) =>
        Break

      case List(Id("continue")) =>
        Continue

      case List(Id("if"), test, left) =>
        state.progs.if_(expr(scope, test), stmt(scope, body, left), Block(Nil, Nil))

      case List(Id("if"), test, left, right) =>
        state.progs.if_(expr(scope, test), stmt(scope, body, left), stmt(scope, body, right))

      case List(Id("while"), test, prog) =>
        val prog_ = stmt(scope, body, prog)
        state.progs.while_(expr(scope, test), prog_, modifies(prog_))

      case List(Id("label" | "goto"), _*) =>
        Error.raise("not supported", "labels and gotos")

      case _ =>
        Error.raise("not a statement", cuvee.smtlib.Parser.head(from))

  def kind(tagged: Tagged): Kind =
    if tagged.contract.isEmpty then Kind.Loop else Kind.Body

  // the properties of the statement `tagged` of kind `kind`, written `inline` as its annotation or in an annotate-tag
  // command, whose values are resolved: formulas for location invariants, invariants and contracts, which are those
  // of the core, integers for termination measures, and names for tags; other attributes, e.g. :named, are kept
  def properties(tagged: Tagged, kind: Kind, inline: Boolean, from: List[Any]): Attrs =
    val scope = tagged.scope
    val contract = tagged.contract.getOrElse(scope)

    val attrs_ =
      for (kw, arg) <- annotations(from)
      yield (kw, arg) match
        case ("tag", Some(Id(tag))) if inline && kind != Kind.Statement =>
          val tag_ : Name = tag
          kw -> Some(tag_)

        case ("tag", _) if inline =>
          Error.raise("tag on a statement that is neither a loop nor the body of a procedure", arg.getOrElse(kw))

        case ("tag", _) =>
          Error.raise("tag in an annotate-tag command", arg.getOrElse(kw))

        case ("check-true", Some(phi)) =>
          kw -> Some(formula(tagged, scope, phi))

        case ("invariant", Some(phi)) if kind == Kind.Loop =>
          kw -> Some(formula(tagged, scope, phi))

        // the precondition is evaluated at the entry, where the old values are the current ones (see State.declare)
        case ("requires", Some(phi)) if kind == Kind.Body =>
          kw -> Some(Old.elim(Nil, Nil, formula(tagged, contract, phi)))

        case ("ensures", Some(phi)) if kind == Kind.Body =>
          kw -> Some(formula(tagged, contract, phi))

        case ("decreases", Some(arg)) if kind != Kind.Statement =>
          kw -> Some(integer(tagged, contract, arg))

        case ("invariant" | "requires" | "ensures" | "decreases", _) =>
          Error.raise("property not allowed on this statement", kw, kind)

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

        Error.report("at refers to a tag other than that of the body of the procedure", from):
          require(tagged.body == Some(tag_))

        Error.report("at refers to a variable that is neither global nor an input", from):
          require(tagged.entry.contains(x_))

        List(Id("old"), Id(x))

      case List(Id("at" | "final"), _*) =>
        Error.raise("not supported", from)

      case List(args*) =>
        args.toList.map(at(tagged, _))

      case _ =>
        from

  // the properties are resolved by the kind of the first statement with the tag
  override def annotate(tag: Name, from: List[Any]): Cmd =
    Error.report("unknown tag", tag):
      require(tags.contains(tag))

    val tagged = tags(tag).head
    linked(tag, properties(tagged, kind(tagged), false, from))
