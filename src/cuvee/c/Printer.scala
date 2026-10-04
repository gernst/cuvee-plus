package cuvee.c

import util.Name
import cuvee.Error
import cuvee.core._

import easyprint.Doc
import easyprint.Doc.{text, space, line, linebreak, hardline, empty, concat, join, render}
import easyprint.Group
import easyprint.Nest

import easyparse.Assoc

// prints procedures as C functions, as far as they are C programs: integers are int, Bool is _Bool,
// arrays Array Int T are T a[] (as values); assertions and assumptions are written with the conventions of SV-COMP;
// C's / and % are recognized in their translation to div and mod of SMT-LIB (see Quot and Rem),
// other occurrences of div and mod are written in terms of / and %; quantifiers and other constructs raise an error;
// commands that are not part of C, e.g. assertions, are printed by the SMT-LIB printer
object Printer extends cuvee.pipe.Printer:
  val width = 80

  // the result of the procedure that is printed, which return writes
  var result: Option[Var] = None

  val names = Map(
    "=" -> "==",
    "not" -> "!",
    "and" -> "&&",
    "or" -> "||"
  )

  // C has no $ in names, the index follows an underscore
  def name(name: Name): String =
    name.suffixed("_")

  def commas(docs: List[Doc]): Doc =
    join(docs, text(",") ++ line)

  def call(fun: String, args: List[Doc]): Doc =
    Group(text(fun + "(") ++ Nest(2, linebreak ++ commas(args)) ++ text(")"))

  // models are printed as C functions, those that are not C, e.g. with quantifiers, as in SMT-LIB
  def lines(res: Result): List[String] =
    res match
      case Model(decls) =>
        for
          decl <- decls
          line <-
            try lines(decl)
            catch case _: Error => cuvee.smtlib.Printer.lines(decl)
        yield line

      case _ =>
        cuvee.smtlib.Printer.lines(res)

  // each command is followed by an empty line, as by the SMT-LIB printer
  def lines(cmd: Cmd): List[String] =
    cmd match
      case _: DeclareVar | _: DeclareProc | _: DefineProc | _: DefineFun =>
        render(doc(cmd), width) :+ ""

      case _ =>
        cuvee.smtlib.Printer.lines(cmd)

  def lines(typ: Type): List[String] =
    render(doc(typ), width)

  def lines(expr: Expr): List[String] =
    render(doc(expr), width)

  def lines(prog: Prog): List[String] =
    render(doc(prog), width)

  def doc(typ: Type): Doc =
    typ match
      case Sort.int  => text("int")
      case Sort.bool => text("_Bool")
      case _         => Error.raise("type not supported in C", typ)

  // a declaration of a variable, where arrays have their brackets after the name
  def decl(x: Var): Doc =
    x.typ match
      case Sort(Con.array, List(Sort.int, elem)) =>
        doc(elem) +:+ text(name(x.name) + "[]")

      case typ =>
        doc(typ) +:+ text(name(x.name))

  def returns(out: List[Var]): Doc =
    out match
      case Nil         => text("void")
      case List(res)   => doc(res.typ)
      case _           => Error.raise("several results not supported in C", out)

  def signature(name_ : Name, in: List[Var], out: List[Var]): Doc =
    returns(out) +:+ call(name(name_), if in.isEmpty then List(text("void")) else in.map(decl))

  def doc(cmd: Cmd): Doc =
    cmd match
      case DeclareVar(x, _) =>
        decl(x) ++ text(";")

      case DeclareProc(Proc(name_, Nil, in, out), _) =>
        signature(name_, in, out) ++ text(";")

      // functions, e.g. the predicates of models of Horn clauses
      case DefineFun(Fun(name_, Nil, formals, res), body, _) =>
        val ret = Group(text("return") ++ Nest(2, line ++ doc(body))) ++ text(";")
        doc(res) +:+ call(name(name_), if formals.isEmpty then List(text("void")) else formals.map(decl)) +:+ braces(List(ret))

      case DefineProc(Proc(name_, Nil, in, out), body, _) =>
        result = out.headOption
        try signature(name_, in, out) +:+ block(body)
        finally result = None

      case _ =>
        Error.raise("command not supported in C", cmd)

  def braces(docs: List[Doc]): Doc =
    if docs.isEmpty
    then text("{}")
    else text("{") ++ Nest(2, hardline ++ join(docs, hardline)) ++ hardline ++ text("}")

  // the statements of a block, local variables are declared first,
  // an assignment to the result followed by return is return e
  def statements(prog: Prog): List[Doc] =
    prog match
      case Block(locals, progs) =>
        locals.map(decl(_) ++ text(";")) ++ sequence(progs)

      case _ =>
        List(doc(prog))

  def sequence(progs: List[Prog]): List[Doc] =
    progs match
      case Nil =>
        Nil

      case Assign(List(x), List(e)) :: Return :: rest if result == Some(x) =>
        (Group(text("return") ++ Nest(2, line ++ doc(e))) ++ text(";")) :: sequence(rest)

      case prog :: rest =>
        statements(prog) ++ sequence(rest)

  def block(prog: Prog): Doc =
    braces(statements(prog))

  def nondet(x: Var): Doc =
    val fun = if x.typ == Sort.bool then "__VERIFIER_nondet_bool" else "__VERIFIER_nondet_int"
    text(name(x.name)) +:+ text("=") +:+ text(fun + "();")

  def doc(prog: Prog): Doc =
    prog match
      case Break =>
        text("break;")

      case Continue =>
        text("continue;")

      case Return =>
        result match
          case Some(x) => text("return") +:+ text(name(x.name)) ++ text(";")
          case None    => text("return;")

      case Spec(Nil, True, phi) =>
        call("__VERIFIER_assume", List(doc(phi))) ++ text(";")

      case Spec(Nil, phi, True) =>
        call("assert", List(doc(phi))) ++ text(";")

      case Spec(xs, True, True) =>
        join(xs.map(nondet), hardline)

      case Assign(List(x), List(Store(y, index, value))) if x == y =>
        Group(text(name(x.name)) ++ text("[") ++ doc(index) ++ text("]") +:+ text("=") ++ Nest(2, line ++ doc(value))) ++ text(";")

      case Assign(List(x), List(rhs)) =>
        Group(text(name(x.name)) +:+ text("=") ++ Nest(2, line ++ doc(rhs))) ++ text(";")

      case Call(proc, args, Nil) =>
        call(name(proc), args.map(doc(_))) ++ text(";")

      case Call(proc, args, List(x)) =>
        text(name(x.name)) +:+ text("=") +:+ call(name(proc), args.map(doc(_))) ++ text(";")

      case Block(_, _) =>
        block(prog)

      case If(test, left, Block(Nil, Nil)) =>
        text("if") +:+ parens(test) +:+ block(left)

      case If(test, left, right: If) =>
        text("if") +:+ parens(test) +:+ block(left) +:+ text("else") +:+ doc(right)

      case If(test, left, right) =>
        text("if") +:+ parens(test) +:+ block(left) +:+ text("else") +:+ block(right)

      case While(test, body, _) =>
        text("while") +:+ parens(test) +:+ block(body)

      case _ =>
        Error.raise("statement not supported in C", prog)

  def parens(expr: Expr): Doc =
    Group(text("(") ++ doc(expr) ++ text(")"))

  // the precedences of C as in the grammar, where ?: binds weakest
  val atomic = Int.MaxValue
  val lowest = -1
  val operand = (atomic - 1, None)

  def prefix(expr: Expr): Option[(String, Int, Expr)] =
    expr match
      case Not(Eq(_, _)) => None
      case Not(arg)      => Some(("!", Grammar.prefix_ops("!"), arg))
      case UMinus.int(arg) => Some(("-", Grammar.prefix_ops("-"), arg))
      case _             => None

  def infix(expr: Expr): Option[(String, Assoc, Int, List[Expr])] =
    def op(op: String, args: List[Expr]) =
      val (assoc, prec) = Grammar.infix_ops(op)
      Some((op, assoc, prec, args))

    // the translations of / and % come first, since they are conditionals and differences
    expr match
      case Quot(a, b)          => op("/", List(a, b))
      case Rem(a, b)           => op("%", List(a, b))
      case App(Trunc.quot, _, _, args) => op("/", args)
      case App(Trunc.rem, _, _, args)  => op("%", args)
      case Not(Eq(a, b))       => op("!=", List(a, b))
      case Eq(a, b)            => op("==", List(a, b))
      case And(args)           => op("&&", args)
      case Or(args)            => op("||", args)
      case Plus.int(args)      => op("+", args)
      case Minus.int(a, b)     => op("-", List(a, b))
      case Times.int(args)     => op("*", args)
      case Lt.int(a, b)        => op("<", List(a, b))
      case Le.int(a, b)        => op("<=", List(a, b))
      case Gt.int(a, b)        => op(">", List(a, b))
      case Ge.int(a, b)        => op(">=", List(a, b))
      case _                   => None

  def level(expr: Expr): (Int, Option[Assoc]) =
    expr match
      case Lit(value: BigInt, _) if value < 0 =>
        (Grammar.prefix_ops("-"), None)

      case Ite(_, _, _) if infix(expr).isEmpty =>
        (lowest, None)

      case _ =>
        prefix(expr) match
          case Some((_, prec, _)) =>
            (prec, None)

          case None =>
            infix(expr) match
              case Some((_, assoc, prec, _)) => (prec, Some(assoc))
              case None                      => (atomic, None)

  def doc(expr: Expr, context: (Int, Option[Assoc])): Doc =
    val (prec, assoc) = level(expr)
    val (min, same) = context

    if prec > min || (prec == min && assoc.isDefined && assoc == same)
    then doc(expr)
    else text("(") ++ doc(expr) ++ text(")")

  def doc(expr: Expr): Doc =
    expr match
      case Var(name_, _) =>
        text(name(name_))

      case Lit(value: BigInt, _) =>
        text(value.toString)

      case True =>
        text("true")

      case False =>
        text("false")

      case Ite(test, left, right) if infix(expr).isEmpty =>
        Group(doc(test, (0, None)) +:+ text("?") +:+ doc(left, (0, None)) +:+ text(":") +:+ doc(right, (lowest, None)))

      case Select(base, index) =>
        doc(base, operand) ++ text("[") ++ doc(index) ++ text("]")

      case _ if prefix(expr).isDefined =>
        val Some((op, prec, arg)) = prefix(expr): @unchecked
        text(op) ++ doc(arg, (prec, None))

      case _ if infix(expr).isDefined =>
        val Some((op, assoc, prec, args)) = infix(expr): @unchecked
        val first = if assoc == Assoc.Left then (prec, Some(Assoc.Left)) else (prec, None)
        val rest = (prec, None)
        val args_ = doc(args.head, first) :: args.tail.map(doc(_, rest))
        Group(args_.head ++ Nest(2, concat(args_.tail.map(line ++ text(op) +:+ _))))

      // C has no let, the bound variables are substituted
      case Let(bound, args, body) =>
        doc(Subst.from(bound, args)(body))

      case Imp(left, right) =>
        doc(Or(Not(left), right))

      // div and mod of SMT-LIB, which differ from C's / and %
      case DivBy.int(a, b) =>
        doc(Trunc.div(a, b))

      case Mod.int(a, b) =>
        doc(Trunc.mod(a, b))

      case _ =>
        Error.raise("expression not supported in C", expr)
