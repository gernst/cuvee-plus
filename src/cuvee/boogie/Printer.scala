package cuvee.boogie

import util.Name
import cuvee.Error
import cuvee.core._
import cuvee.smtlib._
import cuvee.sexpr.Attrs

import easyprint.Doc
import easyprint.Doc.{text, space, line, linebreak, hardline, empty, concat, join, render}
import easyprint.Group
import easyprint.Nest

import easyparse.Assoc

// prints the syntax accepted by the Boogie grammar, such that the output parses back to the same commands;
// constructs that have no counterpart in this syntax raise an error,
// except for commands that are not part of Boogie, which are printed as in the Dafny printer
object Printer extends cuvee.pipe.Printer:
  // the width that documents are laid out for
  val width = 80

  // names of built-in sorts and functions in Boogie, inverse of the translation by the grammar
  val untranslate =
    Grammar.translate.map(_.swap)

  // indexed names are printed with the index as unicode subscript, e.g. a₃
  def name(name: Name): String =
    name match
      case Name(name, None) =>
        untranslate.getOrElse(name, name)

      case _ =>
        name.subscripted

  // elements separated by commas, which go on separate lines if the enclosing group does not fit
  def commas(docs: List[Doc]): Doc =
    join(docs, text(",") ++ line)

  // a call f(a, b, ...) whose arguments go on separate lines if it does not fit
  def call(fun: String, args: List[Doc]): Doc =
    Group(text(fun + "(") ++ Nest(2, linebreak ++ commas(args)) ++ text(")"))

  // string literals have no escapes in Boogie
  def str(value: String): Doc =
    Error.report("string literal with double quotes not supported in Boogie", value):
      require(!value.contains("\""))

    text("\"" + value + "\"")

  // values of options, infos and attributes, which may already be resolved,
  // lists of expressions are the arguments of a single attribute, e.g. of modifies
  def any(value: Any): Doc =
    value match
      case res: Result      => doc(res)
      case cmd: Cmd         => doc(cmd)
      case typ: Type        => doc(typ)
      case expr: Expr       => doc(expr)
      case prog: Prog       => doc(prog)
      case value: String    => str(value)
      case exprs: List[?] if exprs.forall(_.isInstanceOf[Expr]) =>
        commas(exprs.map(expr => doc(expr.asInstanceOf[Expr])))
      // attributes that have not been resolved are s-expressions
      case value            => Doc.lines(cuvee.sexpr.Printer.lines(value))

  def lines(res: Result): List[String] =
    render(doc(res), width)

  def lines(cmd: Cmd): List[String] =
    render(doc(cmd), width)

  def lines(typ: Type): List[String] =
    render(doc(typ), width)

  def lines(expr: Expr): List[String] =
    render(doc(expr), width)

  def lines(prog: Prog): List[String] =
    render(doc(prog), width)

  def doc(res: Result): Doc =
    res match
      case Ack.Success =>
        text("success")

      case Ack.Unsupported =>
        text("unsupported")

      // not reported
      case Ack.Done =>
        text("done")

      case Status.Unknown =>
        text("unknown")

      case Status.Sat =>
        text("sat")

      case Status.Unsat =>
        text("unsat")

      case Labels(labels) =>
        Group(text("labels") ++ Nest(2, line ++ commas(labels.map(text)))) ++ text(";")

      case Info(attrs) =>
        Group(join(attrs.attrs.map(attribute), line))

      case Value(value) =>
        any(value)

      case Model(decls) =>
        join(decls.map(doc(_)), hardline)

      case error: Error =>
        val info = error.info.toList.map(value => text("\"" + value.toString.replace("\"", "'") + "\""))
        Group(text("error") +:+ text("\"" + error.msg + "\"") ++ Nest(2, concat(info.map(line ++ _))))

  // commands that are not part of Boogie are statements ending with a semicolon,
  // options and infos are named like attributes
  def doc(cmd: Cmd): Doc =
    cmd match
      case CheckSat =>
        text("check;")

      case Labels =>
        text("labels;")

      case GetModel =>
        text("model;")

      case Exit =>
        text("exit;")

      case Done =>
        Error.raise("internal command cannot be printed", cmd)

      case Push(depth) =>
        text("push") +:+ text(depth.toString) ++ text(";")

      case Pop(depth) =>
        text("pop") +:+ text(depth.toString) ++ text(";")

      case Reset =>
        text("reset;")

      case SetLogic(name) =>
        text("logic") +:+ text(name) ++ text(";")

      case GetOption(name) =>
        text("option") +:+ text(":" + name) ++ text(";")

      case SetOption(name, value) =>
        Group(text("option") +:+ text(":" + name) +:+ text(":=") ++ Nest(2, line ++ any(value)) ++ text(";"))

      case GetInfo(name) =>
        text("info") +:+ text(":" + name) ++ text(";")

      case SetInfo(name, value) =>
        Group(text("info") +:+ text(":" + name) +:+ text(":=") ++ Nest(2, line ++ any(value)) ++ text(";"))

      // the parameters of declared sorts are anonymous
      case DeclareSort(Con(name_, arity), attrs) =>
        text("type") ++ attributes(attrs) +:+ text(name(name_)) ++ params(Type.params("a", arity)) ++ text(";")

      case DefineSort(Con(name_, _), params_, body, attrs) =>
        text("type") ++ attributes(attrs) +:+ text(name(name_)) ++ params(params_) +:+ text("=") +:+ doc(body) ++ text(";")

      case DeclareDatatypes(_, _, _) =>
        Error.raise("datatypes not supported in Boogie", cmd)

      // constants have no type parameters in Boogie, polymorphic ones are functions without arguments
      case DeclareFun(Fun(name_, Nil, Nil, res), attrs) =>
        text("const") ++ attributes(attrs) +:+ text(name(name_)) ++ text(":") +:+ doc(res) ++ text(";")

      case DeclareFun(Fun(name_, params_, formals_, res), attrs) =>
        signature(text("function") ++ attributes(attrs), name(name_), params_, formals_) ++ text(":") +:+ doc(res) ++ text(";")

      // constants are defined as functions without arguments
      case DefineFun(Fun(name_, params_, formals_, res), body, attrs) =>
        val sig = signature(text("function") ++ attributes(attrs), name(name_), params_, formals_) ++ text(":") +:+ doc(res)
        Group(sig +:+ text("{") ++ Nest(2, line ++ doc(body)) ++ line ++ text("}"))

      case Assert(Axiom, _, phi, attrs) =>
        Group(text("axiom") ++ attributes(attrs) ++ Nest(2, line ++ doc(phi))) ++ text(";")

      // goals and lemmas are not part of Boogie, they are printed like axioms with their own keyword
      case Assert(justify, _, phi, attrs) =>
        Group(text(format(justify)) ++ attributes(attrs) ++ Nest(2, line ++ doc(phi))) ++ text(";")

      case DeclareVar(Var(name_, typ), attrs) =>
        text("var") ++ attributes(attrs) +:+ text(name(name_)) ++ text(":") +:+ doc(typ) ++ text(";")

      // the signature of a procedure without body ends with a semicolon
      case DeclareProc(Proc(name_, params_, in, out), attrs) =>
        val head = signature(text("procedure") ++ attributes(attrs), name(name_), params_, in) ++ returns(out) ++ text(";")
        header(head, clauses(attrs), None)

      case DefineProc(Proc(name_, params_, in, out), body, attrs) =>
        val head = signature(text("procedure") ++ attributes(attrs), name(name_), params_, in) ++ returns(out)
        header(head, clauses(attrs), Some(block(body)))

  def format(justify: Justify) =
    justify match
      case Axiom => "axiom"
      case Goal  => "goal"
      case Lemma => "lemma"

  // type parameters in angle brackets
  def params(params: List[Param]): Doc =
    if params.isEmpty
    then empty
    else text("<") ++ join(params.map(doc(_)), text(",") ++ space) ++ text(">")

  // the keyword and name of a function or procedure with its type parameters and formal parameters
  def signature(head: Doc, name: String, params_ : List[Param], formals_ : List[Var]): Doc =
    Group(head +:+ text(name) ++ params(params_) ++ text("(") ++ Nest(2, linebreak ++ formals(formals_)) ++ text(")"))

  def returns(out: List[Var]): Doc =
    if out.isEmpty
    then empty
    else space ++ Group(text("returns (") ++ Nest(2, linebreak ++ formals(out)) ++ text(")"))

  // attributes that are printed as specification clauses of procedures and loops,
  // provided that they have been resolved
  def isClause(name: String, arg: Option[Any]): Boolean =
    (name, arg) match
      case ("requires" | "ensures" | "invariant", Some(_: Expr)) => true
      case ("modifies", Some(xs: List[?])) => xs.forall(_.isInstanceOf[Var])
      case _ => false

  // the arguments of an attribute are separated by commas, e.g. those of modifies
  def attribute(name: String, arg: Option[Any]): Doc =
    arg match
      case None =>
        text("{:" + name + "}")

      case Some(arg) =>
        Group(text("{:" + name) ++ Nest(2, line ++ any(arg)) ++ text("}"))

  // the remaining attributes, each preceded by a space, written after the keyword of a declaration
  def attributes(attrs: Attrs): Doc =
    val attrs_ =
      for (name, arg) <- attrs.attrs if !isClause(name, arg)
      yield space ++ attribute(name, arg)

    concat(attrs_)

  // each clause ends with a semicolon
  def clauses(attrs: Attrs): List[Doc] =
    for case (name, Some(arg)) <- attrs.attrs if isClause(name, Some(arg))
    yield Group(text(name) ++ Nest(2, line ++ any(arg))) ++ text(";")

  // a declaration or loop followed by its specification clauses on separate lines,
  // the body starts on the same line only if there are no clauses
  def header(head: Doc, clauses_ : List[Doc], body: Option[Doc]): Doc =
    val head_ = head ++ Nest(2, concat(clauses_.map(hardline ++ _)))

    body match
      case None =>
        head_

      case Some(body) if clauses_.isEmpty =>
        head_ +:+ body

      case Some(body) =>
        head_ ++ hardline ++ body

  // statements in braces on separate lines
  def braces(docs: List[Doc]): Doc =
    if docs.isEmpty
    then text("{}")
    else text("{") ++ Nest(2, hardline ++ join(docs, hardline)) ++ hardline ++ text("}")

  // the statements of a block, local variables are declared first
  def statements(prog: Prog): List[Doc] =
    prog match
      case Block(Nil, progs) =>
        progs.map(doc(_))

      case Block(locals, progs) =>
        val locals_ = Group(text("var") ++ Nest(2, line ++ formals(locals))) ++ text(";")
        locals_ :: progs.map(doc(_))

      case _ =>
        List(doc(prog))

  def block(prog: Prog): Doc =
    braces(statements(prog))

  val skip: Prog = Block(Nil, Nil)

  def assume(phi: Expr): Doc =
    Group(text("assume") ++ Nest(2, line ++ doc(phi))) ++ text(";")

  def assert(phi: Expr): Doc =
    Group(text("assert") ++ Nest(2, line ++ doc(phi))) ++ text(";")

  def havoc(xs: List[Var]): Doc =
    Group(text("havoc") ++ Nest(2, line ++ commas(xs.map(doc(_))))) ++ text(";")

  // choices are nondeterministic if statements, if (*) { ... } else { ... },
  // nondeterministic iterations are loops without test, while (*) { ... }
  def doc(prog: Prog): Doc =
    prog match
      case Break =>
        text("break;")

      case Continue =>
        Error.raise("continue not supported in Boogie", prog)

      case Return =>
        text("return;")

      case Spec(Nil, True, phi) =>
        assume(phi)

      case Spec(Nil, phi, True) =>
        assert(phi)

      case Spec(xs, True, True) =>
        havoc(xs)

      // general specifications are a sequence of the three statements
      case Spec(xs, pre, post) =>
        val pre_ = if pre == True then Nil else List(assert(pre))
        val xs_ = if xs.isEmpty then Nil else List(havoc(xs))
        val post_ = if post == True then Nil else List(assume(post))
        join(pre_ ++ xs_ ++ post_, hardline)

      case Assign(lhs, rhs) =>
        Group(commas(lhs.map(doc(_))) +:+ text(":=") ++ Nest(2, line ++ commas(rhs.map(doc(_))))) ++ text(";")

      case Call(proc, args, Nil) =>
        text("call") +:+ call(name(proc), args.map(doc(_))) ++ text(";")

      case Call(proc, args, res) =>
        Group(text("call") +:+ commas(res.map(doc(_))) +:+ text(":=") +:+ call(name(proc), args.map(doc(_)))) ++ text(";")

      case Block(_, _) =>
        block(prog)

      case Choice(Nil) =>
        assume(False)

      case Choice(List(prog)) =>
        doc(prog)

      // a conditional as the last branch continues the else if chain
      case Choice(progs) =>
        val last = progs.last match
          case prog: If => doc(prog)
          case prog     => block(prog)
        val branches = progs.init.map(text("if (*)") +:+ block(_)) :+ last
        join(branches, text(" else "))

      case If(test, left, `skip`) =>
        text("if") +:+ parens(test) +:+ block(left)

      // else if chains
      case If(test, left, right: If) =>
        text("if") +:+ parens(test) +:+ block(left) +:+ text("else") +:+ doc(right)

      case If(test, left, right) =>
        text("if") +:+ parens(test) +:+ block(left) +:+ text("else") +:+ block(right)

      case While(test, body, attrs) =>
        loop(parens(test), body, attrs)

      case Iter(body, attrs) =>
        loop(text("(*)"), body, attrs)

      case Ode(_, _, _, _) =>
        Error.raise("differential equations not supported in Boogie", prog)

      case Par(_) =>
        Error.raise("parallel composition not supported in Boogie", prog)

  // loops have no attributes other than their specification clauses in Boogie, e.g. no decreases
  def loop(test: Doc, body: Prog, attrs: Attrs): Doc =
    val other = attrs.attrs.filterNot(isClause(_, _))
    Error.report("attributes of loops not supported in Boogie", other):
      require(other.isEmpty)

    header(text("while") +:+ test, clauses(attrs), Some(block(body)))

  def parens(expr: Expr): Doc =
    Group(text("(") ++ doc(expr) ++ text(")"))

  // types are not broken across lines, arrays are written as maps [k]v
  def doc(typ: Type): Doc =
    typ match
      case Param(name_) =>
        text(name(name_))

      case Sort(Con.array, List(index, value)) =>
        text("[") ++ doc(index) ++ text("]") ++ doc(value)

      case Sort(Con(name_, _), Nil) =>
        text(name(name_))

      case Sort(Con(name_, _), args) =>
        text(name(name_)) ++ text("<") ++ join(args.map(doc(_)), text(",") ++ space) ++ text(">")

  def formals(vars: List[Var]): Doc =
    val formals_ =
      for Var(name_, typ) <- vars
      yield text(name(name_) + ":") +:+ doc(typ)

    commas(formals_)

  // the precedence of an expression in mixfix notation, and the associativity of its operator,
  // atoms bind tightest, quantifiers are always in parentheses and therefore atoms,
  // if-then-else extends as far to the right as possible
  val atomic = Int.MaxValue
  val lowest = -1

  // the bases of map accesses are atoms
  val operand = (atomic - 1, None)

  // the parser resolves a != b to !(a == b)
  def prefix(expr: Expr): Option[(String, Int, Expr)] =
    expr match
      case Not(Eq(_, _)) =>
        None

      case App(fun, _, _, List(arg)) if Grammar.prefix_ops.contains(name(fun.name)) =>
        val op = name(fun.name)
        Some((op, Grammar.prefix_ops(op), arg))

      case _ =>
        None

  // chains with more than two arguments are printed as nested applications, a + b + c is (a + b) + c,
  // chained equations and comparisons, e.g. (= x y z) or (< x y z), are conjunctions of pairs
  def infix(expr: Expr): Option[(String, Assoc, Int, List[Expr])] =
    expr match
      case Not(Eq(a, b)) =>
        val (assoc, prec) = Grammar.infix_ops("!=")
        Some(("!=", assoc, prec, List(a, b)))

      case App(fun, _, _, args) if Grammar.infix_ops.contains(name(fun.name)) =>
        val op = name(fun.name)
        val (assoc, prec) = Grammar.infix_ops(op)

        if args.length == 2 || (args.length > 2 && assoc != Assoc.Non)
        then Some((op, assoc, prec, args))
        else if args.length > 2
        then
          val pairs = for case List(a, b) <- args.sliding(2).toList yield App(fun, List(a, b))
          infix(And(pairs))
        else None

      case Distinct(List(a, b)) =>
        infix(Not(Eq(a, b)))

      // Boogie has no n-ary distinct, it is printed as the conjunction of pairwise disequalities
      case Distinct(exprs) =>
        val pairs = for case a :: rest <- exprs.tails.toList; b <- rest yield Distinct(List(a, b))
        infix(And(pairs))

      case _ =>
        None

  def level(expr: Expr): (Int, Option[Assoc]) =
    expr match
      case Lit(value: BigInt, _) if value < 0 =>
        (Grammar.prefix_ops("-"), None)

      case Ite(_, _, _) =>
        (lowest, None)

      case Let(bound, args, body) =>
        level(Subst.from(bound, args)(body))

      case _ =>
        prefix(expr) match
          case Some((_, prec, _)) =>
            (prec, None)

          case None =>
            infix(expr) match
              case Some((_, assoc, prec, _)) =>
                (prec, Some(assoc))
              case None =>
                (atomic, None)

  // an expression in a context that admits higher precedences,
  // and the same precedence only for operators of the given associativity
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

      case Lit(value: String, _) =>
        str(value)

      case Lit(value, _) =>
        Error.raise("literal not supported in Boogie", expr)

      case Ite(test, left, right) =>
        Group(text("if") +:+ doc(test) ++ line ++ text("then") +:+ doc(left) ++ line ++ text("else") +:+ doc(right))

      case Select(base, index) =>
        doc(base, operand) ++ text("[") ++ doc(index) ++ text("]")

      case Store(base, index, value) =>
        Group(doc(base, operand) ++ text("[") ++ Nest(2, linebreak ++ doc(index) +:+ text(":=") ++ line ++ doc(value)) ++ text("]"))

      case _ if prefix(expr).isDefined =>
        val Some((op, prec, arg)) = prefix(expr): @unchecked
        text(op) ++ doc(arg, (prec, None))

      // a op b op c, which breaks before the operators if it does not fit
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

        Group(args_.head ++ Nest(2, concat(args_.tail.map(line ++ text(op) +:+ _))))

      case App(fun, _, _, Nil) =>
        text(name(fun.name))

      case App(fun, _, _, args) =>
        call(name(fun.name), args.map(doc(_)))

      case Distinct(_) =>
        Error.raise("unprintable distinct", expr)

      case Old(arg) =>
        call("old", List(doc(arg)))

      case Is(_, _) | As(_, _) | Diff(_, _) =>
        Error.raise("not supported in Boogie", expr)

      // quantifiers are always in parentheses
      case Bind(quant @ Name("forall" | "exists", None), bound, body) =>
        Group(text("(") ++ text(name(quant)) +:+ Group(formals(bound)) +:+ text("::") ++ Nest(2, line ++ doc(body)) ++ text(")"))

      case Bind(_, _, _) =>
        Error.raise("binder not supported in Boogie", expr)

      // Boogie has no let, the bound variables are substituted
      case Let(bound, args, body) =>
        doc(Subst.from(bound, args)(body))
