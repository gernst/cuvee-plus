package cuvee.boogie

import util.Name
import cuvee.Error
import cuvee.core._
import cuvee.smtlib._
import cuvee.core.Attrs

import easyprint.Doc
import easyprint.Doc._
import easyprint.Group
import easyprint.Nest
import easyprint.Align

import easyparse.Assoc

// prints the syntax accepted by the Boogie grammar, such that the output parses back to the same commands;
// constructs that have no counterpart in this syntax raise an error,
// except for commands that are not part of Boogie, which are printed as in the Dafny printer
object Printer extends cuvee.pipe.Printer:

  // names of built-in sorts and functions in Boogie, inverse of the translation by the grammar
  val untranslate =
    Grammar.translate.map(_.swap)

  // indexed names are printed with the index as unicode subscript, e.g. a₃; names that are neither identifiers nor
  // operators are escaped by backticks, which Boogie does not have, e.g. seq.++ of the prelude of SMT-LIB
  def name(name: Name): String =
    val name_ =
      name match
        case Name(name, None) =>
          untranslate.getOrElse(name, name)

        case _ =>
          name.subscripted

    if identifier.matches(name_) || Grammar.prefix_ops.contains(name_) || Grammar.infix_ops.contains(name_)
    then name_
    else "`" + name_ + "`"

  // identifiers as accepted by the scanner, including unicode subscripts (see Scanner.flex)
  val identifier = "[a-zA-Z'~#$^_.?`\\\\⁰-⁹₀-₉][a-zA-Z0-9'~#$^_.?`\\\\⁰-⁹₀-₉]*".r

  // elements separated by commas, which go on separate lines if the enclosing group does not fit
  def commas(docs: List[Doc]): Doc =
    join(docs, text(",") ~ line)

  // a call f(a, b, ...) whose arguments go on separate lines if it does not fit
  def call(fun: String, args: List[Doc]): Doc =
    Group(text(fun + "(") ~ Nest(2, linebreak ~ commas(args)) ~ text(")"))

  // string literals escape backslashes and double quotes, as in Dafny
  def str(value: String): Doc =
    text("\"" + util.Strings.escape(value) + "\"")

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
      // attributes that have not been resolved are s-expressions, whose lists are the arguments of the attribute,
      // e.g. the location of a loop, {:location 9, 3, main} for (9 3 main), and whose strings are those of Boogie (see
      // Parser.unresolved); Boogie has no notation for nested lists
      case args: List[?]          => commas(args.map(any))
      case cuvee.sexpr.Str(text)  => str(text)
      case value                  => Doc.lines(cuvee.sexpr.Printer.lines(value))

  def lines(res: Result): List[String] =
    render(doc(res), width)

  // each command is followed by an empty line
  def lines(cmd: Cmd): List[String] =
    render(doc(cmd), width) :+ ""

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

      case Status.Correct =>
        text("correct")

      case Status.Incorrect =>
        text("incorrect")

      case Labels(labels) =>
        Group(text("labels") ~ Nest(2, line ~ commas(labels.map(text)))) ~ text(";")

      case Info(attrs) =>
        Group(join(attrs.attrs.map(attribute), line))

      case Value(value) =>
        any(value)

      case Model(decls) =>
        join(decls.map(doc(_)), hardline)

      case error: Error =>
        val info = error.info.toList.map(value => text("\"" + value.toString.replace("\"", "'") + "\""))
        Group(text("error") ~~ text("\"" + error.msg + "\"") ~ Nest(2, concat(info.map(line ~ _))))

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

      case GetWitness =>
        text("witness;")

      case Exit =>
        text("exit;")

      case Done =>
        Error.raise("internal command cannot be printed", cmd)

      // the commands of SV-LIB, annotate "t" {:check-true x == n}; and verify main();
      case AnnotateTag(tag, attrs) =>
        val attrs_ = for (name, arg) <- attrs.attrs yield line ~ attribute(name, arg)
        Group(text("annotate") ~~ str(tag.indexed) ~ Nest(2, concat(attrs_))) ~ text(";")

      case VerifyCall(proc, args) =>
        text("verify") ~~ call(name(proc), args.map(doc(_))) ~ text(";")

      case Push(depth) =>
        text("push") ~~ text(depth.toString) ~ text(";")

      case Pop(depth) =>
        text("pop") ~~ text(depth.toString) ~ text(";")

      case Reset =>
        text("reset;")

      case SetLogic(name) =>
        text("logic") ~~ text(name) ~ text(";")

      // options and infos are attributes, whose names may contain hyphens
      case GetOption(name) =>
        text("option") ~~ attribute(name, None) ~ text(";")

      case SetOption(name, value) =>
        text("option") ~~ attribute(name, Some(value)) ~ text(";")

      case GetInfo(name) =>
        text("info") ~~ attribute(name, None) ~ text(";")

      case SetInfo(name, value) =>
        text("info") ~~ attribute(name, Some(value)) ~ text(";")

      // the parameters of declared sorts are anonymous
      case DeclareSort(Con(name_, arity), attrs) =>
        text("type") ~ attributes(attrs) ~~ text(name(name_)) ~ params(Type.params("a", arity)) ~ text(";")

      case DefineSort(Con(name_, _), params_, body, attrs) =>
        text("type") ~ attributes(attrs) ~~ text(name(name_)) ~ params(params_) ~~ text("=") ~~ doc(body) ~ text(";")

      // not Boogie, datatypes as in Dafny with the keyword data, mutually recursive ones joined by and
      case DeclareDatatypes(cons, datas, attrs) =>
        val datas_ = for (con, data) <- cons zip datas yield datatype(con, data)
        text("data") ~ attributes(attrs) ~~ join(datas_, hardline ~ text("and") ~ space) ~ text(";")

      // constants have no type parameters in Boogie, polymorphic ones are functions without arguments
      case DeclareFun(Fun(name_, Nil, Nil, res), attrs) =>
        text("const") ~ attributes(attrs) ~~ text(name(name_)) ~ text(":") ~~ doc(res) ~ text(";")

      case DeclareFun(Fun(name_, params_, formals_, res), attrs) =>
        signature(text("function") ~ attributes(attrs), name(name_), params_, formals_) ~ text(":") ~~ doc(res) ~ text(";")

      // constants are defined as functions without arguments
      case DefineFun(Fun(name_, params_, formals_, res), body, attrs) =>
        val sig = signature(text("function") ~ attributes(attrs), name(name_), params_, formals_) ~ text(":") ~~ doc(res)
        Group(sig ~~ text("{") ~ Nest(2, line ~ doc(body)) ~ line ~ text("}"))

      // with type parameters, axiom <a> {:rw} (forall x: a :: φ);
      case Assert(Axiom, params_, phi, attrs) =>
        Group(text("axiom") ~ (if params_.isEmpty then empty else space ~ params(params_)) ~ attributes(attrs) ~ Nest(2, line ~ doc(phi))) ~ text(";")

      // goals and lemmas are not part of Boogie, they are printed like axioms with their own keyword
      case Assert(justify, params_, phi, attrs) =>
        Group(text(format(justify)) ~ (if params_.isEmpty then empty else space ~ params(params_)) ~ attributes(attrs) ~ Nest(2, line ~ doc(phi))) ~ text(";")

      case _: FuseFuns =>
        Error.raise("fuse not supported in Boogie", cmd)

      case DeclareVar(Var(name_, typ), attrs) =>
        text("var") ~ attributes(attrs) ~~ text(name(name_)) ~ text(":") ~~ doc(typ) ~ text(";")

      // the signature of a procedure without body ends with a semicolon
      case DeclareProc(Proc(name_, params_, in, out), attrs) =>
        val head = signature(text("procedure") ~ attributes(attrs), name(name_), params_, in) ~ returns(out) ~ text(";")
        header(head, clauses(attrs), None)

      case DefineProc(Proc(name_, params_, in, out), body, attrs) =>
        val head = signature(text("procedure") ~ attributes(attrs), name(name_), params_, in) ~ returns(out)
        header(head, clauses(attrs), Some(block(body)))

  def format(justify: Justify) =
    justify match
      case Axiom => "axiom"
      case Goal  => "goal"
      case Lemma => "lemma"

  // type parameters in angle brackets
  def datatype(con: Con, data: Datatype): Doc =
    val Datatype(params_, constrs) = data

    val constrs_ =
      for (constr, sels) <- constrs
      yield
        val sels_ =
          for sel <- sels
          yield text(name(sel.name) + ":") ~~ doc(sel.res)

        if sels.isEmpty
        then text(name(constr.name))
        else Group(text(name(constr.name) + "(") ~ Align(join(sels_, text(",") ~ line)) ~ text(")"))

    // the = always goes on the next line, the constructors stay on its line if they fit, aligned by | otherwise
    val head = text(name(con.name)) ~ params(params_)
    head ~ Nest(2, hardline ~ Group(text("=") ~~ join(constrs_, line ~ text("| "))))

  def params(params: List[Param]): Doc =
    if params.isEmpty
    then empty
    else text("<") ~ join(params.map(doc(_)), text(",") ~ space) ~ text(">")

  // the keyword and name of a function or procedure with its type parameters and formal parameters
  def signature(head: Doc, name: String, params_ : List[Param], formals_ : List[Var]): Doc =
    Group(head ~~ text(name) ~ params(params_) ~ text("(") ~ Nest(2, linebreak ~ formals(formals_)) ~ text(")"))

  def returns(out: List[Var]): Doc =
    if out.isEmpty
    then empty
    else space ~ Group(text("returns (") ~ Nest(2, linebreak ~ formals(out)) ~ text(")"))

  // attributes that are printed as specification clauses of procedures and loops,
  // provided that they have been resolved
  def isClause(name: String, arg: Option[Any]): Boolean =
    (name, arg) match
      case ("requires" | "ensures" | "invariant" | "decreases", Some(_: Expr)) => true
      case ("modifies", Some(xs: List[?])) => xs.forall(_.isInstanceOf[Var])
      case _ => false

  // the arguments of an attribute are separated by commas, e.g. those of modifies
  def attribute(name: String, arg: Option[Any]): Doc =
    arg match
      case None =>
        text("{:" + name + "}")

      // the tags of SV-LIB, which need not be identifiers of Boogie, are strings
      case Some(cuvee.sexpr.Id(tag)) if name == "tag" =>
        text("{:" + name) ~~ str(tag) ~ text("}")

      case Some(arg) =>
        Group(text("{:" + name) ~ Nest(2, line ~ any(arg)) ~ text("}"))

  // the remaining attributes, each preceded by a space, written after the keyword of a declaration
  def attributes(attrs: Attrs): Doc =
    val attrs_ =
      for (name, arg) <- attrs.attrs if !isClause(name, arg)
      yield space ~ attribute(name, arg)

    concat(attrs_)

  // each clause ends with a semicolon,
  // the components of a lexicographic termination measure are combined into a single clause
  def clauses(attrs: Attrs): List[Doc] =
    val clauses_ =
      for case (name, Some(arg)) <- attrs.attrs if isClause(name, Some(arg)) && name != "decreases"
      yield Group(text(name) ~ Nest(2, line ~ any(arg))) ~ text(";")

    val dec = attrs.decreases

    if dec.isEmpty
    then clauses_
    else clauses_ :+ (Group(text("decreases") ~ Nest(2, line ~ commas(dec.map(doc(_))))) ~ text(";"))

  // a declaration or loop followed by its specification clauses on separate lines,
  // the body starts on the same line only if there are no clauses
  def header(head: Doc, clauses_ : List[Doc], body: Option[Doc]): Doc =
    val head_ = head ~ Nest(2, concat(clauses_.map(hardline ~ _)))

    body match
      case None =>
        head_

      case Some(body) if clauses_.isEmpty =>
        head_ ~~ body

      case Some(body) =>
        head_ ~ hardline ~ body

  // statements in braces on separate lines
  def braces(docs: List[Doc]): Doc =
    if docs.isEmpty
    then text("{}")
    else text("{") ~ Nest(2, hardline ~ join(docs, hardline)) ~ hardline ~ text("}")

  // the statements of a block, local variables are declared first; a block with attributes is a statement of its own
  def statements(prog: Prog): List[Doc] =
    prog match
      case Block(_, _, attrs) if !attrs.isEmpty =>
        List(doc(prog))

      case Block(Nil, progs, _) =>
        progs.map(doc(_))

      case Block(locals, progs, _) =>
        val locals_ = Group(text("var") ~ Nest(2, line ~ formals(locals))) ~ text(";")
        locals_ :: progs.map(doc(_))

      case _ =>
        List(doc(prog))

  def block(prog: Prog): Doc =
    braces(statements(prog))

  val skip: Prog = Block(Nil, Nil)

  def assume(phi: Expr): Doc =
    Group(text("assume") ~ Nest(2, line ~ doc(phi))) ~ text(";")

  def assert(phi: Expr): Doc =
    Group(text("assert") ~ Nest(2, line ~ doc(phi))) ~ text(";")

  def havoc(xs: List[Var]): Doc =
    Group(text("havoc") ~ Nest(2, line ~ commas(xs.map(doc(_))))) ~ text(";")

  // choices are nondeterministic if statements, if (*) { ... } else { ... },
  // nondeterministic iterations are loops without test, while (*) { ... }
  def doc(prog: Prog): Doc =
    prog match
      case Break =>
        text("break;")

      // not Boogie
      case Continue =>
        text("continue;")

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
        Group(commas(lhs.map(doc(_))) ~~ text(":=") ~ Nest(2, line ~ commas(rhs.map(doc(_))))) ~ text(";")

      case Call(proc, args, Nil, _) =>
        text("call") ~~ call(name(proc), args.map(doc(_))) ~ text(";")

      case Call(proc, args, res, _) =>
        Group(text("call") ~~ commas(res.map(doc(_))) ~~ text(":=") ~~ call(name(proc), args.map(doc(_)))) ~ text(";")

      // the attributes of a block, e.g. the tags of SV-LIB, precede its braces
      case prog @ Block(_, _, attrs) if !attrs.isEmpty =>
        join(attrs.attrs.map(attribute(_, _)), space) ~~ block(prog.copy(attrs = Attrs.empty))

      case Block(_, _, _) =>
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
        val branches = progs.init.map(text("if (*)") ~~ block(_)) :+ last
        join(branches, text(" else "))

      case If(test, left, `skip`) =>
        text("if") ~~ parens(test) ~~ block(left)

      // else if chains
      case If(test, left, right: If) =>
        text("if") ~~ parens(test) ~~ block(left) ~~ text("else") ~~ doc(right)

      case If(test, left, right) =>
        text("if") ~~ parens(test) ~~ block(left) ~~ text("else") ~~ block(right)

      case While(test, body, attrs) =>
        loop(parens(test), body, attrs)

      case Iter(body, attrs) =>
        loop(text("(*)"), body, attrs)

      case Ode(_, _, _, _, _) =>
        Error.raise("differential equations not supported in Boogie")

      case Par(_) =>
        Error.raise("parallel composition not supported in Boogie")

  // the attributes of a loop other than its specification clauses follow the keyword, as in Dafny, which Boogie does
  // not have, e.g. the tags of SV-LIB and the locations of loops in C
  def loop(test: Doc, body: Prog, attrs: Attrs): Doc =
    header(text("while") ~ attributes(attrs) ~~ test, clauses(attrs), Some(block(body)))

  def parens(expr: Expr): Doc =
    Group(text("(") ~ Align(doc(expr)) ~ text(")"))

  // types are not broken across lines, arrays are written as maps [k]v, nested ones as maps of several indices [k, l]v
  def doc(typ: Type): Doc =
    typ match
      case Param(name_) =>
        text(name(name_))

      case BitVec(n) =>
        text("bv" + n)

      case Arrays(indices, value) =>
        text("[") ~ join(indices.map(doc), text(", ")) ~ text("]") ~ doc(value)

      case Sort(Con(name_, _), Nil) =>
        text(name(name_))

      case Sort(Con(name_, _), args) =>
        text(name(name_)) ~ text("<") ~ join(args.map(doc(_)), text(",") ~ space) ~ text(">")

  def formals(vars: List[Var]): Doc =
    val formals_ =
      for Var(name_, typ) <- vars
      yield text(name(name_) + ":") ~~ doc(typ)

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

      // fractions n.0 / d.0, whose sign is part of the numerator
      case Lit(value: util.Rational, _) if value.den != 1 && (if value.isNegative then -value else value).decimal.isEmpty =>
        val (assoc, prec) = Grammar.infix_ops("/")
        (prec, Some(assoc))

      case Lit(value: util.Rational, _) if value.isNegative =>
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
    else text("(") ~ Align(doc(expr)) ~ text(")")

  // the dependencies of a combinator, which are broken across lines as a group of their own, aligned
  def dependencies(deps: List[Expr]): Doc =
    Group(Align(commas(deps.map(doc(_)))))

  // a combinator, whose head is followed by the initial values of a trace, the dependencies after for, the keyword
  // with the bound variables, and the updates, one per accumulator, each a single expression or guarded cases,
  // case guard => result ...; if it does not fit, the keyword goes below for and the updates below the keyword,
  // indented (as in Dafny)
  def combinator(head: Doc, inits: List[Expr], deps: List[Expr], keyword: String, bound: List[Var], results: List[Expr]): Doc =
    def result(update: Expr): Doc =
      update match
        case Eps(updates) =>
          val cases =
            for Upd(cond, rhs) <- updates
            yield text("case") ~~ doc(cond) ~~ text("=>") ~~ doc(rhs)
          Group(cases.reduce(_ ~ line ~ _))

        case _ =>
          doc(update)

    val updates_ = commas(results.map(result))

    // the bound variables are never broken across lines; the initial values precede the dependencies, on their own
    // line when there are several
    val binders = text(bound.map(x => name(x.name)).mkString(", ") + " ::")
    val inits_ =
      inits match
        case Nil       => empty
        case List(one) => doc(one) ~ text(",") ~ space
        case _         => Group(commas(inits.map(doc(_)))) ~ text(",") ~ line
    val body = inits_ ~ text("for") ~~ dependencies(deps) ~ line ~ text(keyword) ~~ binders ~ Nest(2, line ~ updates_)
    Group(head ~ Align(body) ~ text(")"))

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
      case Lit(value: util.Rational, typ) if value.isNegative =>
        (-value).decimal match
          case Some(digits) => text("-" + digits)
          case None         => text("-") ~ doc(Lit(-value, typ))

      case Lit(value: util.Rational, typ) =>
        value.decimal match
          case Some(digits) => text(digits)
          case None         => doc(Lit(util.Rational(value.num), typ)) ~~ text("/") ~~ doc(Lit(util.Rational(value.den), typ))

      case Lit(value, _) =>
        Error.raise("literal not supported in Boogie", expr)

      case Ite(test, left, right) =>
        Group(text("if") ~~ doc(test) ~ line ~ text("then") ~~ doc(left) ~ line ~ text("else") ~~ doc(right))

      // like the alternatives of Dafny's if statement, if { case p => x case q => y },
      // which is delimited by the braces and never parenthesized
      case Eps(updates) =>
        val cases =
          for Upd(cond, rhs) <- updates
          yield line ~ text("case") ~~ doc(cond) ~~ text("=>") ~~ doc(rhs)
        Group(text("if {") ~ Nest(2, concat(cases)) ~ line ~ text("}"))

      // like the types, nested selections and updates are those of several indices, a[i, j] and a[i, j := v]
      case Arrays.select(base, indices) =>
        doc(base, operand) ~ text("[") ~ commas(indices.map(doc)) ~ text("]")

      case Arrays.store(base, indices, value) =>
        Group(doc(base, operand) ~ text("[") ~ Nest(2, linebreak ~ commas(indices.map(doc)) ~~ text(":=") ~ line ~ doc(value)) ~ text("]"))

      case _ if prefix(expr).isDefined =>
        val Some((op, prec, arg)) = prefix(expr): @unchecked
        text(op) ~ doc(arg, (prec, None))

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

        Group(args_.head ~ Nest(2, concat(args_.tail.map(line ~ text(op) ~~ _))))

      // all but the last element of a trace
      case Butlast(arg) =>
        text("⌊") ~ doc(arg) ~ text("⌋")

      case App(fun, _, _, Nil) =>
        text(name(fun.name))

      case App(fun, _, _, args) =>
        call(name(fun.name), args.map(doc(_)))

      case Distinct(_) =>
        Error.raise("unprintable distinct", expr)

      // the combinators of trace equation systems; a trace with several accumulators lists their initial values, then
      // the accumulators before the bound variables, and one result per accumulator (as in Dafny)
      case Trace(inits, deps, accs, bound, results) =>
        combinator(text("trace("), inits, deps, "do", accs ++ bound, results)

      case Maps(deps, bound, update) =>
        combinator(text("map("), Nil, deps, "yield", bound, List(update))

      case Invs(deps, bound, body) =>
        combinator(text("all("), Nil, deps, "check", bound, List(body))

      // the component i of the last value and the history of a trace of several accumulators, current(S).i and ⌊S⌋.i
      case Component(trace, i) =>
        doc(Current(trace)) ~ text("." + i)

      case History(trace, i) =>
        doc(Butlast(trace)) ~ text("." + i)

      case Old(arg) =>
        call("old", List(doc(arg)))

      case Is(_, _) | As(_, _) | Diff(_, _) | Prop(_, _) | Match(_, _) =>
        Error.raise("not supported in Boogie", expr)

      // quantifiers are always in parentheses
      case Bind(quant @ Name("forall" | "exists", None), bound, body) =>
        Group(text("(") ~ Align(text(name(quant)) ~~ Group(Align(formals(bound))) ~~ text("::") ~ Nest(2, line ~ doc(body))) ~ text(")"))

      case Bind(_, _, _) =>
        Error.raise("binder not supported in Boogie", expr)

      // lambdas are always in parentheses, like quantifiers, nested ones are maps of several indices
      case Lams(bound, body) =>
        Group(text("(") ~ Align(text("lambda") ~~ Group(Align(formals(bound))) ~~ text("::") ~ Nest(2, line ~ doc(body))) ~ text(")"))

      case Lam(_, _, _) =>
        Error.raise("lambda of function type not supported in Boogie", expr)

      // recursive functions are internal, without syntax
      case Rec(_, _) =>
        Error.raise("recursive function not supported in Boogie", expr)

      // Boogie has no let, the bound variables are substituted
      case Let(bound, args, body) =>
        doc(Subst.from(bound, args)(body))
