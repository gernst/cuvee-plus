package cuvee.c

import util.Name
import cuvee.Error
import cuvee.core._

import easyprint.Doc
import easyprint.Doc._
import easyprint.Group
import easyprint.Nest
import easyprint.Align

import easyparse.Assoc

// prints procedures as C functions, as far as they are C programs: integers are int, Bool is _Bool,
// arrays Array Int T are T a[] (as values), arrays of arrays T a[][], initializers of constant arrays at their
// declarations; the result of a function is a local variable result, which each return returns, and which the parser
// reads back as the result itself; assertions and assumptions are written with the conventions of SV-COMP;
// the functions of the prelude of C (resources/cuvee/c/prelude.bpl) are written as the C they stand for;
// uninterpreted functions are prototypes, and their applications calls;
// everything else is printed in SMT-LIB, wrapped such that it looks like a macro, SMT_LIB(...),
// e.g. assertions of formulas, quantifiers, and commands such as check-sat, as far down as possible,
// e.g. a quantifier in an assertion of a procedure; contracts and the invariants and variants of loops are annotations
// of ACSL, as are assertions with quantifiers or implications, without the zero values of global variables as the
// precondition of main, which C input has implicitly;
// results, e.g. models, are not programs, they are printed in SMT-LIB
object Printer extends cuvee.pipe.Printer:

  // the result of the procedure that is printed, which return writes
  var result: Option[Var] = None

  // whether an annotation of ACSL is printed, and the result of the procedure as \result in its postconditions
  var acsl: Boolean = false
  var returns: Option[Var] = None

  val names = Map(
    "=" -> "==",
    "not" -> "!",
    "and" -> "&&",
    "or" -> "||"
  )

  // C has no $ in names, the index follows an underscore,
  // names without index that end like that get another underscore, e.g. tmp_1 of the input is not the temporary tmp₁
  def name(name: Name): String =
    if name.index.isEmpty && name.name.matches(".*_[0-9]+")
    then name.name + "_"
    else name.suffixed("_")

  def commas(docs: List[Doc]): Doc =
    join(docs, text(",") ~ line)

  def call(fun: String, args: List[Doc]): Doc =
    Group(text(fun + "(") ~ Nest(2, linebreak ~ commas(args)) ~ text(")"))

  def lines(res: Result): List[String] =
    cuvee.smtlib.Printer.lines(res)

  // what is not C in SMT-LIB, whose lines are aligned after SMT_LIB(
  def smtlib(lines: List[String]): Doc =
    text("SMT_LIB(") ~ Align(join(lines.map(text), hardline)) ~ text(")")

  // each command is followed by an empty line, as by the SMT-LIB printer
  def lines(cmd: Cmd): List[String] =
    render(doc(cmd), width) :+ ""

  def lines(typ: Type): List[String] =
    render(doc(typ), width)

  // expressions occur in reports, e.g. of goals that do not hold
  def lines(expr: Expr): List[String] =
    render(doc(expr), width)

  def lines(prog: Prog): List[String] =
    render(doc(prog), width)

  def doc(typ: Type): Doc =
    typ match
      case Sort.int  => text("int")
      case Sort.bool => text("_Bool")
      // the pointers of the background theory of C (resources/cuvee/c/prelude.bpl)
      case Sort(Con(Name("Void", None), 0), Nil)            => text("void")
      case Sort(Con(Name("Ptr", None), 1), List(elem))      => doc(elem) ~ text(" *")
      case _         => smtlib(cuvee.smtlib.Printer.lines(typ))

  // the element type and the number of dimensions of arrays of arrays, e.g. int a[][] for Array Int (Array Int Int)
  def dims(typ: Type): (Type, Int) =
    typ match
      case Sort(Con.array, List(Sort.int, elem)) =>
        val (base, n) = dims(elem)
        (base, n + 1)

      case _ =>
        (typ, 0)

  // a declaration of a variable, where arrays have their brackets after the name, one per dimension
  def decl(x: Var): Doc =
    x.typ match
      case Sort(Con.array, List(Sort.int, _)) =>
        val (base, n) = dims(x.typ)
        doc(base) ~~ text(name(x.name) + "[]" * n)

      case Sort(Con(Name("Ptr", None), 1), List(elem)) =>
        doc(elem) ~~ text("*" + name(x.name))

      case typ =>
        doc(typ) ~~ text(name(x.name))

  def returns(out: List[Var]): Doc =
    out match
      case Nil         => text("void")
      case List(res)   => doc(res.typ)
      case _           => Error.raise("several results not supported in C", out)

  def signature(name_ : Name, in: List[Var], out: List[Var]): Doc =
    returns(out) ~~ call(name(name_), if in.isEmpty then List(text("void")) else in.map(decl))

  // the commands that are not C, e.g. assertions, and procedures of several results, are printed in SMT-LIB
  def doc(cmd: Cmd): Doc =
    cmd match
      case DeclareVar(x, _) =>
        decl(x) ~ text(";")

      case DeclareProc(Proc(name_, Nil, in, out), attrs) if out.length <= 1 =>
        contract(name_, out, attrs) ~ signature(name_, in, out) ~ text(";")

      // uninterpreted functions, e.g. the predicates of Horn clauses
      case DeclareFun(Fun(name_, Nil, formals, res), _) =>
        doc(res) ~~ call(name(name_), if formals.isEmpty then List(text("void")) else formals.map(decl)) ~ text(";")

      // contracts are omitted, e.g. the zero values of global variables as the precondition of main
      // the result is a local variable, assigned as in the input, which each return returns,
      // such that its value is arbitrary if it is not assigned, as in Dafny
      case DefineProc(Proc(name_, Nil, in, out), body, attrs) if out.length <= 1 =>
        result = out.headOption
        try contract(name_, out, attrs) ~ signature(name_, in, out) ~~ braces(out.map(decl(_) ~ text(";")) ++ statements(body))
        finally result = None

      case _ =>
        smtlib(cuvee.smtlib.Printer.command(cmd))

  // the clauses of an annotation of ACSL, /*@ requires ...; ensures ...; */, each on a line of its own
  def annotation(clauses: List[(String, Expr)]): Doc =
    acsl = true
    try
      val docs = clauses.map((kw, e) => Group(text(kw) ~ Nest(2, line ~ doc(e))) ~ text(";"))
      text("/*@") ~ Nest(2, hardline ~ join(docs, hardline)) ~ hardline ~ text("*/")
    finally acsl = false

  // the contract of a procedure followed by a line break, if any, without the precondition of main that the global
  // variables are zero (see zeros), which the parser adds again
  def contract(name_ : Name, out: List[Var], attrs: Attrs): Doc =
    val requires = attrs.values[Expr]("requires").filterNot(phi => name_ == Name("main", None) && zeros(phi))
    val clauses =
      requires.map("requires" -> _) ++ attrs.values[Expr]("ensures").map("ensures" -> _) ++
        attrs.values[Expr]("decreases").map("decreases" -> _)
    if clauses.isEmpty
    then empty
    else
      returns = out.headOption
      try annotation(clauses) ~ hardline
      finally returns = None

  // equations of variables with the zero values of their types, false, null, and constant arrays of those
  def zeros(phi: Expr): Boolean =
    def zero(e: Expr): Boolean =
      e match
        case Lit(value: BigInt, _)                                         => value == 0
        case False                                                         => true
        case App(Fun(Name("null", None), _, Nil, _), _, _, Nil)            => true
        case App(Fun(Name("const", None), _, _, _), _, _, List(arg))       => zero(arg)
        case _                                                             => false

    phi match
      case And(args)     => args.forall(zeros)
      case Eq(_: Var, e) => zero(e)
      case _             => false

  // the invariants and variants of a loop followed by a line break, if any
  def invariants(attrs: Attrs): Doc =
    val clauses = attrs.invariants.map("loop invariant" -> _) ++ attrs.decreases.map("loop variant" -> _)
    if clauses.isEmpty then empty else annotation(clauses) ~ hardline

  // whether an expression is not C, but ACSL: quantifiers, implications, and old values
  def logical(expr: Expr): Boolean =
    expr match
      case Bind(_, _, _) | Imp(_, _) | Old(_) => true
      case App(_, _, _, args)                 => args.exists(logical)
      case _                                  => false

  def braces(docs: List[Doc]): Doc =
    if docs.isEmpty
    then text("{}")
    else text("{") ~ Nest(2, hardline ~ join(docs, hardline)) ~ hardline ~ text("}")

  // the statements of a block, local variables are declared first, with their initializers (see initializer)
  def statements(prog: Prog): List[Doc] =
    prog match
      case Block(locals, progs, _) =>
        val inits =
          for
            x <- locals
            i = progs.indexWhere(_.free.contains(x))
            if i >= 0
            items <- initializer(x, progs(i))
          yield (x, i, items)

        val decls =
          for x <- locals
          yield inits.find(_._1 == x) match
            case Some((_, _, items)) => Group(decl(x) ~~ text("=") ~ Nest(2, line ~ text("{") ~ commas(items.map(doc(_))) ~ text("}"))) ~ text(";")
            case None                => decl(x) ~ text(";")

        decls ++ sequence(progs.zipWithIndex.collect { case (prog, i) if !inits.exists(_._2 == i) => prog })

      case _ =>
        List(doc(prog))

  def sequence(progs: List[Prog]): List[Doc] =
    progs match
      case Nil =>
        Nil

      case prog :: rest =>
        statements(prog) ++ sequence(rest)

  def block(prog: Prog): Doc =
    braces(statements(prog))

  // the nondeterministic functions of SV-COMP by the ranges of their integer types (see Parser.havoc), where long is
  // printed as long long or int, whichever has its range
  val ranges: Map[(BigInt, BigInt), String] =
    val types =
      for
        (bytes, name) <- List(1 -> "char", 2 -> "short", 4 -> "int", 8 -> "longlong")
        signed <- List(true, false)
      yield
        val bits = 8 * bytes
        if signed
        then (-BigInt(2).pow(bits - 1), BigInt(2).pow(bits - 1) - 1) -> name
        else (BigInt(0), BigInt(2).pow(bits) - 1) -> ("u" + name)
    types.toMap

  def nondet(x: Var): Doc =
    val fun = if x.typ == Sort.bool then "__VERIFIER_nondet_bool" else "__VERIFIER_nondet_int"
    text(name(x.name)) ~~ text("=") ~~ text(fun + "();")

  def doc(prog: Prog): Doc =
    prog match
      case Break =>
        text("break;")

      case Continue =>
        text("continue;")

      case Return =>
        result match
          case Some(x) => text("return") ~~ text(name(x.name)) ~ text(";")
          case None    => text("return;")

      case Spec(Nil, True, phi) =>
        call("__VERIFIER_assume", List(doc(phi))) ~ text(";")

      case Spec(Nil, phi, True) if logical(phi) =>
        annotation(List("assert" -> phi))

      case Spec(Nil, phi, True) =>
        call("assert", List(doc(phi))) ~ text(";")

      case Spec(xs, True, True) =>
        join(xs.map(nondet), hardline)

      // nondeterministic values within the range of an integer type (see Parser.havoc)
      case Spec(List(x), True, And(List(Ints.le(Lit(lo: BigInt, _), y), Ints.le(z, Lit(hi: BigInt, _)))))
          if x == y && x == z && ranges.contains((lo, hi)) =>
        text(name(x.name)) ~~ text("=") ~~ text("__VERIFIER_nondet_" + ranges((lo, hi)) + "();")

      // nondeterministic values with another postcondition, e.g. 0 <= x for __VERIFIER_nondet_uint with -unbounded
      case Spec(xs, True, phi) =>
        join(xs.map(nondet), hardline) ~ hardline ~ call("__VERIFIER_assume", List(doc(phi))) ~ text(";")

      case Assign(List(x), List(Store(y, index, value))) if x == y =>
        val (indices, value_) = update(Select(x, index), value)
        val lhs = (index :: indices).map(i => text("[") ~ doc(i) ~ text("]"))
        Group(text(name(x.name)) ~ lhs.fold(empty)(_ ~ _) ~~ text("=") ~ Nest(2, line ~ doc(value_))) ~ text(";")

      case Assign(List(x), List(rhs)) =>
        Group(text(name(x.name)) ~~ text("=") ~ Nest(2, line ~ doc(rhs))) ~ text(";")

      case Call(proc, args, Nil) =>
        call(name(proc), args.map(doc(_))) ~ text(";")

      case Call(proc, args, List(x)) =>
        text(name(x.name)) ~~ text("=") ~~ call(name(proc), args.map(doc(_))) ~ text(";")

      case Block(_, _, _) =>
        block(prog)

      case If(test, left, Block(Nil, Nil, _)) =>
        text("if") ~~ parens(test) ~~ block(left)

      case If(test, left, right: If) =>
        text("if") ~~ parens(test) ~~ block(left) ~~ text("else") ~~ doc(right)

      case If(test, left, right) =>
        text("if") ~~ parens(test) ~~ block(left) ~~ text("else") ~~ block(right)

      case While(test, body, attrs) =>
        invariants(attrs) ~ text("while") ~~ parens(test) ~~ block(body)

      case _ =>
        smtlib(cuvee.smtlib.Printer.lines(prog)) ~ text(";")

  // the items of the initializer of an array `x` from its first statement in a block, which is moved to its declaration,
  // int a[] = { 97, 65 }: an assignment of a constant array of zeros, const(0) of the prelude of C, or constant(0),
  // the name of it in the Dafny translations of SV-COMP, whose positions 0, 1, ... are updated with closed values
  def initializer(x: Var, prog: Prog): Option[List[Expr]] =
    def items(expr: Expr): Option[List[Expr]] =
      expr match
        case App(Fun(Name("const" | "constant", None), _, _, _), _, _, List(Lit(zero: BigInt, _))) if zero == 0 =>
          Some(Nil)

        case Store(base, Lit(index: BigInt, _), value) if value.free.isEmpty =>
          items(base).filter(_.length == index)
            .map(_ :+ value)

        case _ =>
          None

    (prog, x.typ) match
      case (Assign(List(`x`), List(expr)), Sort(Con.array, List(Sort.int, elem))) if dims(elem)._2 == 0 =>
        items(expr).filter(_.nonEmpty)

      case _ =>
        None

  // the further indices and the value of an update of an element of an array of arrays, a[i][j] = v,
  // i.e. a := store(a, i, store(select(a, i), j, v)), where `base` is select(a, i)
  def update(base: Expr, value: Expr): (List[Expr], Expr) =
    value match
      case Store(base_, index, value_) if base_ == base =>
        val (indices, value__) = update(Select(base, index), value_)
        (index :: indices, value__)

      case _ =>
        (Nil, value)

  def parens(expr: Expr): Doc =
    Group(text("(") ~ Align(doc(expr)) ~ text(")"))

  // the precedences of C as in the grammar, where ?: binds weakest
  val atomic = Int.MaxValue
  val lowest = -1
  val operand = (atomic - 1, None)

  def prefix(expr: Expr): Option[(String, Int, Expr)] =
    expr match
      case Not(Eq(_, _)) => None
      case Not(arg)      => Some(("!", Grammar.prefix_ops("!"), arg))
      case Ints.uminus(arg) => Some(("-", Grammar.prefix_ops("-"), arg))
      case App(Fun(Name("bitnot", None), Nil, _, _), _, _, List(arg)) => Some(("~", Grammar.prefix_ops("~"), arg))
      // the overflow of unsigned integers as casts, e.g. uint(x + 1) as (unsigned int) (x + 1), which parse back to it
      case App(Fun(Name(f, None), Nil, _, _), _, _, List(arg)) if Syntax.overflows.contains(f) =>
        Some(("(" + Syntax.overflows(f) + ") ", Grammar.prefix_ops("-"), arg))
      case _             => None

  def infix(expr: Expr): Option[(String, Assoc, Int, List[Expr])] =
    def op(op: String, args: List[Expr]) =
      val (assoc, prec) = Grammar.infix_ops(op)
      Some((op, assoc, prec, args))

    expr match
      // the connectives of ACSL, where equations of truth values are equivalences
      case Imp(a, b) if acsl                     => op("==>", List(a, b))
      case Eq(a, b) if acsl && a.typ == Sort.bool => op("<==>", List(a, b))
      case Not(Eq(a, b))       => op("!=", List(a, b))
      case Eq(a, b)            => op("==", List(a, b))
      case And(args)           => op("&&", args)
      case Or(args)            => op("||", args)
      // the arguments as they are, not flattened, such that x * (y * z) keeps its parentheses
      case App(Ints.plus.fun, _, _, args)  => op("+", args)
      case Ints.minus(a, b)     => op("-", List(a, b))
      case App(Ints.times.fun, _, _, args) => op("*", args)
      // the division and remainder of C (see resources/cuvee/c/prelude.bpl), unlike div and mod of SMT-LIB
      case App(Fun(Name("quot", None), Nil, _, _), _, _, List(a, b)) => op("/", List(a, b))
      case App(Fun(Name("rem", None), Nil, _, _), _, _, List(a, b))  => op("%", List(a, b))
      // shifts by constants, which are divisions by powers of 2 that round down (see Parser.arith)
      case App(Fun(Name("div", None), Nil, _, _), _, _, List(a, Lit(n: BigInt, _))) if n > 1 && n.bitCount == 1 =>
        op(">>", List(a, Lit(BigInt(n.bitLength - 1), Sort.int)))
      // the bit operations and shifts of the prelude of C
      case App(Fun(Name("bitand", None), Nil, _, _), _, _, List(a, b))    => op("&", List(a, b))
      case App(Fun(Name("bitor", None), Nil, _, _), _, _, List(a, b))     => op("|", List(a, b))
      case App(Fun(Name("bitxor", None), Nil, _, _), _, _, List(a, b))    => op("^", List(a, b))
      case App(Fun(Name("shl", None), Nil, _, _), _, _, List(a, b))       => op("<<", List(a, b))
      case App(Fun(Name("shr", None), Nil, _, _), _, _, List(a, b))       => op(">>", List(a, b))
      case Ints.lt(a, b)        => op("<", List(a, b))
      case Ints.le(a, b)        => op("<=", List(a, b))
      case Ints.gt(a, b)        => op(">", List(a, b))
      case Ints.ge(a, b)        => op(">=", List(a, b))
      case _                   => None

  def level(expr: Expr): (Int, Option[Assoc]) =
    expr match
      case prelude(expr_) =>
        level(expr_)

      case Lit(value: BigInt, _) if value < 0 =>
        (Grammar.prefix_ops("-"), None)

      case Ite(_, _, _) if infix(expr).isEmpty =>
        (lowest, None)

      case Bind(_, _, _) if acsl =>
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
    else text("(") ~ Align(doc(expr)) ~ text(")")

  // the functions of the prelude of C (resources/cuvee/c/prelude.bpl) as C, truth(x) is x != 0, number(b) is b ? 1 : 0
  object prelude:
    def unapply(expr: Expr): Option[Expr] =
      expr match
        case App(Fun(Name("truth", None), Nil, _, _), _, _, List(arg))  => Some(Not(Eq(arg, Ints.zero)))
        case App(Fun(Name("number", None), Nil, _, _), _, _, List(arg)) => Some(Ite(arg, Ints.one, Ints.zero))
        case _                                                        => None

  def doc(expr: Expr): Doc =
    expr match
      case prelude(expr_) =>
        doc(expr_)

      case x: Var if acsl && returns.contains(x) =>
        text("\\result")

      case Var(name_, _) =>
        text(name(name_))

      case Lit(value: BigInt, _) =>
        text(value.toString)

      case True if acsl =>
        text("\\true")

      case False if acsl =>
        text("\\false")

      case True =>
        text("true")

      case False =>
        text("false")

      case Old(arg) if acsl =>
        text("\\old(") ~ Align(doc(arg)) ~ text(")")

      // quantifiers of ACSL over the mathematical integers and the truth values
      case Bind(quant, bound, body) if acsl && (quant == All.name || quant == Ex.name) && bound.forall(x => x.typ == Sort.int || x.typ == Sort.bool) =>
        val binders = bound.map(x => text(if x.typ == Sort.int then "integer" else "boolean") ~~ text(name(x.name)))
        Group(text("\\" + quant.name) ~~ commas(binders) ~ text(";") ~ Nest(2, line ~ doc(body)))

      // the null pointer constant
      case App(Fun(Name("null", None), _, Nil, _), _, _, Nil) =>
        text("0")

      case Ite(test, left, right) if infix(expr).isEmpty =>
        Group(doc(test, (0, None)) ~~ text("?") ~~ doc(left, (0, None)) ~~ text(":") ~~ doc(right, (lowest, None)))

      case Select(base, index) =>
        doc(base, operand) ~ text("[") ~ doc(index) ~ text("]")

      case _ if prefix(expr).isDefined =>
        val Some((op, prec, arg)) = prefix(expr): @unchecked
        text(op) ~ doc(arg, (prec, None))

      case _ if infix(expr).isDefined =>
        val Some((op, assoc, prec, args)) = infix(expr): @unchecked
        val first = if assoc == Assoc.Left then (prec, Some(Assoc.Left)) else (prec, None)
        val last = if assoc == Assoc.Right then (prec, Some(Assoc.Right)) else (prec, None)
        val inner = (prec, None)
        val args_ =
          for (arg, i) <- args.zipWithIndex
          yield
            if i == 0 then doc(arg, first)
            else if i == args.length - 1 then doc(arg, last)
            else doc(arg, inner)
        Group(args_.head ~ Nest(2, concat(args_.tail.map(line ~ text(op) ~~ _))))

      // C has no let, the bound variables are substituted
      case Let(bound, args, body) =>
        doc(Subst.from(bound, args)(body))

      // other functions, e.g. the predicates of Horn clauses
      case App(fun, Nil, _, Nil) =>
        text(name(fun.name))

      case App(fun, Nil, _, args) =>
        call(name(fun.name), args.map(doc(_)))

      case _ =>
        smtlib(cuvee.smtlib.Printer.lines(expr))
