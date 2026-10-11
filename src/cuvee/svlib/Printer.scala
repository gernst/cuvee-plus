package cuvee.svlib

import cuvee.Error
import cuvee.core._
import cuvee.core.Attrs

// SV-LIB output: the logic is SMT-LIB, procedures and loops are printed with their properties as annotations
// (! s attrs), where the local variables of a procedure are those of the block of its body (see Parser),
// location invariants (assertions) annotate the empty statement; modifies clauses are dropped, since SV-LIB infers
// them; not supported: blocks with local variables elsewhere, polymorphic procedures and procedures without body,
// iterations, differential equations and parallel composition
object Printer extends cuvee.pipe.Printer:
  import cuvee.sexpr.Printer.atom
  import cuvee.sexpr.Printer.list
  import cuvee.smtlib.Printer.mangle
  import cuvee.smtlib.Printer.app
  import cuvee.smtlib.Printer.apps
  import cuvee.smtlib.Printer.kw
  import cuvee.smtlib.Printer.formals
  import cuvee.smtlib.Printer.eqs

  def lines(res: Result): List[String] =
    cuvee.smtlib.Printer.lines(res)

  def lines(typ: Type): List[String] =
    cuvee.smtlib.Printer.lines(typ)

  def lines(expr: Expr): List[String] =
    cuvee.smtlib.Printer.lines(expr)

  // each command is followed by an empty line
  def lines(cmd: Cmd): List[String] =
    command(cmd) :+ ""

  // the properties of a procedure or loop, without its modifies clause
  def properties(attrs: Attrs): List[String] =
    cuvee.smtlib.Printer.lines(Attrs(attrs.attrs.filterNot(_._1 == "modifies")))

  // (! s attrs), or s without attributes
  def annotated(prog: List[String], attrs: List[String]): List[String] =
    if attrs.isEmpty
    then prog
    else apps(atom("!"), prog, attrs)

  def command(cmd: Cmd): List[String] =
    cmd match
      case DefineProc(Proc(name, Nil, in, out), body, attrs) =>
        val (locals, progs) =
          body match
            case Block(locals, progs, _) => (locals, progs)
            case _                    => (Nil, List(body))

        val body_ = annotated(apps(atom("sequence"), lines(progs)), properties(attrs))
        apps(atom("define-proc"), mangle(name), list(formals(in)), list(formals(out)), list(formals(locals)), body_)

      case _: DefineProc | _: DeclareProc =>
        Error.raise("not supported in SV-LIB", cmd)

      case _ =>
        cuvee.smtlib.Printer.command(cmd)

  def lines(prog: Prog): List[String] =
    prog match
      case Break =>
        app("break")

      case Continue =>
        app("continue")

      case Return =>
        app("return")

      case Spec(Nil, True, True) =>
        app("sequence")

      case Spec(Nil, True, phi) =>
        apps(atom("assume"), lines(phi))

      case Spec(Nil, phi, True) =>
        apps(atom("!"), app("sequence"), kw("check-true"), lines(phi))

      case Spec(xs, True, True) =>
        apps(atom("havoc"), lines(xs))

      case Assign(lhs, rhs) =>
        apps(atom("assign"), eqs(lhs, rhs))

      case Call(proc, args, res) =>
        apps(atom("call"), mangle(proc), list(lines(args)), list(lines(res)))

      case Block(Nil, progs, attrs) =>
        annotated(apps(atom("sequence"), lines(progs)), properties(attrs))

      case Choice(progs) =>
        apps(atom("choice"), lines(progs))

      case If(test, left, Block(Nil, Nil, attrs)) if attrs.isEmpty =>
        apps(atom("if"), lines(test), lines(left))

      case If(test, left, right) =>
        apps(atom("if"), lines(test), lines(left), lines(right))

      case While(test, body, attrs) =>
        annotated(apps(atom("while"), lines(test), lines(body)), properties(attrs))

      case _ =>
        Error.raise("not supported in SV-LIB", prog)
