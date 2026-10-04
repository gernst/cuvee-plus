package cuvee.dafny

import util.Name
import util.Rational
import cuvee.Error
import cuvee.core._
import cuvee.smtlib._
import cuvee.sexpr.Atom
import cuvee.core.Attrs

import easyprint.Doc
import easyprint.Doc.{text, space, line, linebreak, hardline, empty, concat, join, render}
import easyprint.Group
import easyprint.Nest
import easyprint.Align

import easyparse.Assoc

object Printer extends cuvee.pipe.Printer:
  // the width that documents are laid out for
  val width = 80

  // names of built-in sorts and functions in Dafny, inverse of the translation by the grammar
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

  // string literals escape backslashes and double quotes
  def str(value: String): Doc =
    text("\"" + value.replace("\\", "\\\\").replace("\"", "\\\"") + "\"")

  // values of options, infos and attributes, which may already be resolved
  def any(value: Any): Doc =
    value match
      case res: Result      => doc(res)
      case cmd: Cmd         => doc(cmd)
      case typ: Type        => doc(typ)
      case expr: Expr       => doc(expr)
      case prog: Prog       => doc(prog)
      // e.g. the variables of a modifies clause
      case exprs: List[?] if exprs.nonEmpty && exprs.forall(_.isInstanceOf[Expr]) =>
        commas(exprs.map { case expr: Expr => doc(expr) })
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
        val info = error.info.toList.map(value => str(value.toString))
        Group(text("error") +:+ str(error.msg) ++ Nest(2, concat(info.map(line ++ _))))

  // commands that are not part of Dafny are statements ending with a semicolon,
  // options and infos are named like attributes
  def doc(cmd: Cmd): Doc =
    cmd match
      case CheckSat =>
        text("check")

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
        text("type") ++ attributes(attrs) +:+ text(name(name_)) ++ params(Type.params("a", arity))

      case DefineSort(Con(name_, _), params_, body, attrs) =>
        text("type") ++ attributes(attrs) +:+ text(name(name_)) ++ params(params_) +:+ text("=") +:+ doc(body)

      // mutually recursive datatypes are declared one after another
      case DeclareDatatypes(cons, datas, attrs) =>
        val datas_ =
          for (con, data) <- cons zip datas
          yield datatype(con, data, attrs)

        join(datas_, hardline)

      case DeclareFun(Fun(name_, params_, Nil, res), attrs) =>
        header(text("const") ++ attributes(attrs) +:+ text(name(name_)) ++ params(params_) ++ text(":") +:+ doc(res), attrs, None)

      case DeclareFun(Fun(name_, params_, formals_, res), attrs) =>
        val sig = signature(name(name_), params_, formals_) ++ text(":") +:+ doc(res)
        header(text("function") ++ attributes(attrs) +:+ sig, attrs, None)

      case DefineFun(Fun(name_, params_, Nil, res), body, attrs) =>
        val head = text("const") ++ attributes(attrs) +:+ text(name(name_)) ++ params(params_) ++ text(":") +:+ doc(res)
        Group(head +:+ text(":=") ++ Nest(2, line ++ doc(body)))

      case DefineFun(Fun(name_, params_, formals_, res), body, attrs) =>
        val sig = signature(name(name_), params_, formals_) ++ text(":") +:+ doc(res)
        header(text("function") ++ attributes(attrs) +:+ sig, attrs, Some(braces(List(doc(body)))))

      // the type parameters of assertions are implicit
      case Assert(justify, _, phi, attrs) =>
        Group(text(format(justify)) ++ attributes(attrs) ++ Nest(2, line ++ doc(phi)))

      // global variables are not Dafny, which has fields of objects instead
      case DeclareVar(Var(name_, typ), attrs) =>
        text("var") ++ attributes(attrs) +:+ text(name(name_)) ++ text(":") +:+ doc(typ) ++ text(";")

      case DeclareProc(Proc(name_, params_, in, out), attrs) =>
        header(text("method") ++ attributes(attrs) +:+ signature(name(name_), params_, in) ++ returns(out), attrs, None)

      case DefineProc(Proc(name_, params_, in, out), body, attrs) =>
        header(text("method") ++ attributes(attrs) +:+ signature(name(name_), params_, in) ++ returns(out), attrs, Some(block(body)))

  // goals and lemmas are not part of Dafny, they are printed like axioms with their own keyword
  def format(justify: Justify) =
    justify match
      case Axiom => "axiom"
      case Goal  => "goal"
      case Lemma => "lemma"

  // names A, B, C, ... for the parameters of declared sorts
  def params(params: List[Param]): Doc =
    if params.isEmpty
    then empty
    else text("<") ++ join(params.map(doc(_)), text(",") ++ space) ++ text(">")

  // the name of a function or method with its type parameters and formal parameters
  def signature(name: String, params_ : List[Param], formals_ : List[Var]): Doc =
    Group(text(name) ++ params(params_) ++ text("(") ++ Nest(2, linebreak ++ formals(formals_)) ++ text(")"))

  def returns(out: List[Var]): Doc =
    if out.isEmpty
    then empty
    else space ++ Group(text("returns (") ++ Nest(2, linebreak ++ formals(out)) ++ text(")"))

  // selectors are declared without the qualification with the datatype, which the parser adds again
  def selector(con: Con, sel: Fun): String =
    name(sel.name).stripPrefix(name(con.name) + "_")

  def datatype(con: Con, data: Datatype, attrs: Attrs): Doc =
    val Datatype(params_, constrs) = data

    val constrs_ =
      for (constr, sels) <- constrs
      yield
        val sels_ =
          for sel <- sels
          yield text(selector(con, sel) + ":") +:+ doc(sel.res)

        if sels.isEmpty
        then text(name(constr.name))
        else call(name(constr.name), sels_)

    val head = text("datatype") ++ attributes(attrs) +:+ text(name(con.name)) ++ params(params_) +:+ text("=")
    Group(head ++ Nest(2, line ++ join(constrs_, line ++ text("| "))))

  // attributes that are printed as contract clauses of functions, methods, and loops,
  // provided that they have been resolved
  def isClause(name: String, arg: Option[Any]): Boolean =
    (name, arg) match
      case ("requires" | "ensures" | "invariant" | "decreases" | "assumes" | "commits", Some(_: Expr)) => true
      case ("modifies", Some(xs: List[?])) => xs.forall(_.isInstanceOf[Var])
      case _ => false

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

  // the components of a lexicographic termination measure are combined into a single clause
  def clauses(attrs: Attrs): List[Doc] =
    val clauses_ =
      for case (name, Some(arg)) <- attrs.attrs if isClause(name, Some(arg)) && name != "decreases"
      yield Group(text(name) ++ Nest(2, line ++ any(arg)))

    val dec = attrs.decreases

    if dec.isEmpty
    then clauses_
    else clauses_ :+ Group(text("decreases") ++ Nest(2, line ++ commas(dec.map(doc(_)))))

  // a declaration or loop followed by its contract clauses on separate lines,
  // the body starts on the same line only if there are no clauses
  def header(head: Doc, attrs: Attrs, body: Option[Doc]): Doc =
    val clauses_ = clauses(attrs)
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

  // statements that are not part of Dafny:
  // choices are nondeterministic if statements, if * { ... } else { ... },
  // nondeterministic iterations are loops without test, while * { ... },
  // differential equations with evolution constraint are x', y' == e, f && dom invariant ...;
  // general specifications name the modified variables, spec x, y requires pre ensures post;
  def doc(prog: Prog): Doc =
    prog match
      case Break =>
        text("break;")

      case Continue =>
        text("continue;")

      case Return =>
        text("return;")

      case Spec(Nil, True, phi) =>
        Group(text("assume") ++ Nest(2, line ++ doc(phi))) ++ text(";")

      case Spec(Nil, phi, True) =>
        Group(text("assert") ++ Nest(2, line ++ doc(phi))) ++ text(";")

      case Spec(xs, True, True) =>
        Group(text("havoc") ++ Nest(2, line ++ commas(xs.map(doc(_))))) ++ text(";")

      case Spec(xs, pre, post) =>
        val head = if xs.isEmpty then text("spec") else text("spec") +:+ commas(xs.map(doc(_)))
        val pre_ = Group(text("requires") ++ Nest(2, line ++ doc(pre)))
        val post_ = Group(text("ensures") ++ Nest(2, line ++ doc(post)))
        Group(head ++ Nest(2, line ++ pre_ ++ line ++ post_)) ++ text(";")

      case Assign(lhs, rhs) =>
        Group(commas(lhs.map(doc(_))) +:+ text(":=") ++ Nest(2, line ++ commas(rhs.map(doc(_))))) ++ text(";")

      case Call(proc, args, Nil) =>
        call(name(proc), args.map(doc(_))) ++ text(";")

      case Call(proc, args, res) =>
        Group(commas(res.map(doc(_))) +:+ text(":=") +:+ call(name(proc), args.map(doc(_)))) ++ text(";")

      case Block(_, _) =>
        block(prog)

      case Choice(Nil) =>
        text("assume false;")

      case Choice(List(prog)) =>
        doc(prog)

      case Choice(progs) =>
        val branches = progs.init.map(text("if *") +:+ block(_)) :+ block(progs.last)
        join(branches, text(" else "))

      case If(test, left, `skip`) =>
        text("if") +:+ doc(test) +:+ block(left)

      // else if chains
      case If(test, left, right: If) =>
        text("if") +:+ doc(test) +:+ block(left) +:+ text("else") +:+ doc(right)

      case If(test, left, right) =>
        text("if") +:+ doc(test) +:+ block(left) +:+ text("else") +:+ block(right)

      case While(test, body, attrs) =>
        header(text("while") ++ attributes(attrs) +:+ doc(test), attrs, Some(block(body)))

      case Iter(body, attrs) =>
        header(text("while") ++ attributes(attrs) +:+ text("*"), attrs, Some(block(body)))

      // the right hand sides bind tighter than the conjunction with the evolution constraint
      case Ode(xs, rhs, dom, attrs) =>
        val lhs_ = commas(xs.map(x => text(name(x.name) + "'")))
        val rhs_ = commas(rhs.map(doc(_, (Grammar.infix_ops("&&")._2, None))))
        val dom_ = if dom == True then Nil else List(line ++ text("&&") +:+ doc(dom))
        val ode = Group(lhs_ +:+ text("==") ++ Nest(2, line ++ rhs_ ++ concat(dom_)))
        header(ode, attrs, None) ++ text(";")

      case Par(calls) =>
        text("parallel {") ++ Nest(2, concat(calls.map(hardline ++ doc(_)))) ++ hardline ++ text("}")

  // types are not broken across lines
  def doc(typ: Type): Doc =
    typ match
      case Param(name_) =>
        text(name(name_))

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
  // atoms bind tightest, binders, let and if-then-else extend as far to the right as possible
  val atomic = Int.MaxValue
  val lowest = -1

  // the bases of array accesses are atoms
  val operand = (atomic - 1, None)

  def prefix(expr: Expr): Option[(String, Int, Expr)] =
    expr match
      // a != b, see infix
      case Not(Eq(_, _)) =>
        None

      case App(fun, _, _, List(arg)) if Grammar.prefix_ops.contains(name(fun.name)) =>
        val op = name(fun.name)
        Some((op, Grammar.prefix_ops(op), arg))

      case _ =>
        None

  // chains with more than two arguments are printed as nested applications, a + b + c is (a + b) + c,
  // which is wrong for chainable relations;
  // chained equations and comparisons, e.g. x == y == z or x < y <= z,
  // are not supported for now (see Grammar.infix_ops) and are printed like function calls, e.g. ==(x, y, z)
  def infix(expr: Expr): Option[(String, Assoc, Int, List[Expr])] =
    expr match
      // sequence literals are atoms
      case _ if elems(expr).isDefined =>
        None

      // concatenation and prefix of sequences are overloaded in Dafny, x in s is containment of [x]
      case App(fun, _, _, args @ List(_, _)) if fun == Fun.seq.concat =>
        infix(App(fun.copy(name = Name("+", None)), Nil, Sort.bool, args))

      case App(fun, _, _, args @ List(_, _)) if fun == Fun.seq.prefixof =>
        infix(App(fun.copy(name = Name("<=", None)), Nil, Sort.bool, args))

      case App(fun, _, _, List(seq, App(unit, _, _, List(elem)))) if fun == Fun.seq.contains && unit == Fun.seq.unit =>
        infix(App(fun.copy(name = Name("in", None)), Nil, Sort.bool, List(elem, seq)))

      case App(fun, _, _, args) if Grammar.infix_ops.contains(name(fun.name)) =>
        val op = name(fun.name)
        val (assoc, prec) = Grammar.infix_ops(op)
        val chain = assoc != Assoc.Non && op != "==" && op != "!="
        if args.length == 2 || (args.length > 2 && chain)
        then Some((op, assoc, prec, args))
        else None

      case Not(Eq(a, b)) =>
        infix(Distinct(List(a, b)))

      case Distinct(List(a, b)) =>
        val (assoc, prec) = Grammar.infix_ops("!=")
        Some(("!=", assoc, prec, List(a, b)))

      // Dafny has no n-ary distinct, it is printed as the conjunction of pairwise disequalities
      case Distinct(exprs) =>
        val pairs = for case a :: rest <- exprs.tails.toList; b <- rest yield Distinct(List(a, b))
        infix(And(pairs))

      case _ =>
        None

  // the elements of sequence literals, [], [a], and concatenations of these
  def elems(expr: Expr): Option[List[Expr]] =
    expr match
      case App(fun, _, _, Nil) if fun == Fun.seq.empty =>
        Some(Nil)

      case App(fun, _, _, List(elem)) if fun == Fun.seq.unit =>
        Some(List(elem))

      case App(fun, _, _, List(left, right)) if fun == Fun.seq.concat =>
        for left_ <- elems(left); right_ <- elems(right)
        yield left_ ++ right_

      case _ =>
        None

  def level(expr: Expr): (Int, Option[Assoc]) =
    expr match
      // binds tighter than all operators, but is not an operand of accesses
      case As(_, _) =>
        (atomic - 1, None)

      case Lit(value: BigInt, _) if value < 0 =>
        (Grammar.prefix_ops("-"), None)

      // fractions n.0 / d.0, whose sign is part of the numerator
      case Lit(value: Rational, _) if value.den != 1 && (if value.isNegative then -value else value).decimal.isEmpty =>
        val (assoc, prec) = Grammar.infix_ops("/")
        (prec, Some(assoc))

      case Lit(value: Rational, _) if value.isNegative =>
        (Grammar.prefix_ops("-"), None)

      case Ite(_, _, _) | Bind(_, _, _) | Let(_, _, _) =>
        (lowest, None)

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

  // the dependencies of a combinator, which are broken across lines as a group of their own, aligned
  def dependencies(deps: List[Expr]): Doc =
    Group(Align(commas(deps.map(doc(_)))))

  // the update of a combinator, a single expression or guarded cases, if guard then result, ...
  def combinator(head: Doc, keyword: String, bound: List[Var], update: List[(Expr, Expr)]): Doc =
    val update_ =
      update match
        case List((True, result)) =>
          doc(result)

        case _ =>
          commas(for (guard, result) <- update yield text("if") +:+ doc(guard) +:+ text("then") +:+ doc(result))

    // the bound variables are never broken across lines, the update goes on a line of its own if it does not fit
    val binders = text(bound.map(x => name(x.name)).mkString(", ") + " =>")
    Group(head +:+ text(keyword) +:+ binders ++ Nest(2, line ++ update_) ++ text(")"))

  // chains of the same operator are flattened in the direction of its associativity, a && b && c,
  // such that the operators are aligned when they are broken across lines
  def chain(op: String, assoc: Assoc, args: List[Expr]): List[Expr] =
    def same(arg: Expr) =
      infix(arg) match
        case Some((`op`, `assoc`, _, args_)) => Some(args_)
        case _                               => None

    assoc match
      case Assoc.Left if args.nonEmpty =>
        same(args.head) match
          case Some(args_) => chain(op, assoc, args_) ++ args.tail
          case None        => args

      case Assoc.Right if args.nonEmpty =>
        same(args.last) match
          case Some(args_) => args.init ++ chain(op, assoc, args_)
          case None        => args

      case _ =>
        args

  def doc(expr: Expr): Doc =
    expr match
      case Var(name_, _) =>
        text(name(name_))

      case Lit(value: BigInt, _) =>
        text(value.toString)

      case Lit(value: String, _) =>
        str(value)

      // real literals always have a decimal point, 2.0, otherwise they would be parsed as integers,
      // rationals that have no finite decimal expansion are written as fractions, 1.0 / 3.0
      case Lit(value: Rational, typ) if value.isNegative =>
        (-value).decimal match
          case Some(digits) => text("-" + digits)
          case None         => text("-") ++ doc(Lit(-value, typ))

      case Lit(value: Rational, typ) =>
        value.decimal match
          case Some(digits) => text(digits)
          case None         => doc(Lit(Rational(value.num), typ)) +:+ text("/") +:+ doc(Lit(Rational(value.den), typ))

      case Lit(value, _) =>
        Error.raise("unprintable literal", expr)

      case Ite(test, left, right) =>
        Group(text("if") +:+ doc(test) ++ line ++ text("then") +:+ doc(left) ++ line ++ text("else") +:+ doc(right))

      case _ if elems(expr).isDefined =>
        val Some(elems_) = elems(expr): @unchecked
        Group(text("[") ++ Nest(2, linebreak ++ commas(elems_.map(doc(_)))) ++ text("]"))

      case App(fun, _, _, List(seq)) if fun == Fun.seq.len =>
        text("|") ++ doc(seq) ++ text("|")

      case App(fun, _, _, List(seq, index)) if fun == Fun.seq.nth =>
        doc(seq, operand) ++ text("[") ++ doc(index) ++ text("]")

      case App(fun, _, _, List(seq, index, App(unit, _, _, List(value)))) if fun == Fun.seq.update && unit == Fun.seq.unit =>
        Group(doc(seq, operand) ++ text("[") ++ Nest(2, linebreak ++ doc(index) +:+ text(":=") ++ line ++ doc(value)) ++ text("]"))

      // the length is the difference of the bounds, s[i..j] is extract(s, i, j - i)
      case App(fun, _, _, List(seq, from, len)) if fun == Fun.seq.extract =>
        val to = len match
          case Minus.int(to, `from`)       => to
          case _ if from == Lit(BigInt(0), Sort.int) => len
          case _                           => Plus.int(from, len)
        doc(seq, operand) ++ text("[") ++ doc(from) ++ text("..") ++ doc(to) ++ text("]")

      case App(fun, _, _, _) if (Fun.seq.all contains fun) && infix(expr).isEmpty =>
        Error.raise("not supported in Dafny", expr)

      case Select(base, index) =>
        doc(base, operand) ++ text("[") ++ doc(index) ++ text("]")

      case Store(base, index, value) =>
        Group(doc(base, operand) ++ text("[") ++ Nest(2, linebreak ++ doc(index) +:+ text(":=") ++ line ++ doc(value)) ++ text("]"))

      case _ if prefix(expr).isDefined =>
        val Some((op, prec, arg)) = prefix(expr): @unchecked
        text(op) ++ doc(arg, (prec, None))

      // a op b op c, which breaks before the operators if it does not fit
      case _ if infix(expr).isDefined =>
        val Some((op, assoc, prec, args__)) = infix(expr): @unchecked
        val args = chain(op, assoc, args__)
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

      // two or more arguments are printed in infix notation above
      case Distinct(_) =>
        Error.raise("unprintable distinct", expr)

      // the combinators of trace equation systems
      case Trace(init, deps, acc, bound, update) =>
        val head = text("trace(") ++ doc(init) ++ text(",") +:+ text("for") +:+ dependencies(deps)
        combinator(head, "do", acc :: bound, update)

      case Maps(deps, bound, update) =>
        combinator(text("map(for") +:+ dependencies(deps), "yield", bound, update)

      case Invs(deps, bound, body) =>
        combinator(text("all(for") +:+ dependencies(deps), "check", bound, List((True, body)))

      case Old(arg) =>
        call("old", List(doc(arg)))

      case Diff(xs, arg) =>
        Group(text("(") ++ commas(xs.map(doc(_))) +:+ text("::") ++ Nest(2, line ++ doc(arg)) ++ text(")'"))

      // testers are parsed on variables only
      case Is(x: Var, fun) =>
        doc(x) ++ text("." + name(fun.name) + "?")

      case Is(_, _) =>
        Error.raise("tester on an expression that is not a variable not supported in Dafny", expr)

      case As(arg, typ) =>
        doc(arg, operand) +:+ text("as") +:+ doc(typ)

      case Bind(quant, bound, body) =>
        Group(text(name(quant)) +:+ Group(Align(formals(bound))) +:+ text("::") ++ Nest(2, line ++ doc(body)))

      case Let(bound, args, body) =>
        Group(text("var") +:+ formals(bound) +:+ text(":=") +:+ commas(args.map(doc(_))) ++ text(";") ++ line ++ doc(body))
