package cuvee.dafny

import util.Name
import util.Rational
import cuvee.Error
import cuvee.core._
import cuvee.smtlib._
import cuvee.core.Attrs
import cuvee.sexpr

import easyprint.Doc
import easyprint.Doc._
import easyprint.Group
import easyprint.Nest
import easyprint.Align

import easyparse.Assoc

object Printer extends cuvee.pipe.Printer:

  // names of built-in sorts and functions in Dafny, inverse of the translation by the grammar
  val untranslate =
    Grammar.translate.map(_.swap)

  // indexed names are printed with the index as unicode subscript, e.g. a₃;
  // names that are neither identifiers nor operators are escaped by backticks, which Dafny does not have,
  // e.g. the instances `length<Int>` of Monomorph
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

  // identifiers as accepted by the scanner, including unicode subscripts, and primed ones x' (see Grammar.id_prime)
  val identifier = "[a-zA-Z_][a-zA-Z0-9⁰-⁹₀-₉_~#$?']*".r

  // elements separated by commas, which go on separate lines if the enclosing group does not fit
  def commas(docs: List[Doc]): Doc =
    join(docs, text(",") ~ line)

  // elements separated by commas, which flow up to the width of the line, aligned after a line break
  def flow(docs: List[Doc]): Doc =
    Align(Doc.fill(docs, text(",")))

  // a call f(a, b, ...) whose arguments flow up to the width of the line, aligned after the opening parenthesis
  def call(fun: String, args: List[Doc]): Doc =
    text(fun + "(") ~ flow(args) ~ text(")")

  // string literals escape backslashes and double quotes
  def str(value: String): Doc =
    text("\"" + util.Strings.escape(value) + "\"")

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
        Group(text("labels") ~ Nest(2, line ~ commas(labels.map(text))))

      case Info(attrs) =>
        Group(join(attrs.attrs.map(attribute), line))

      case Value(value) =>
        any(value)

      // the definitions are separated by empty lines, like commands
      case Model(decls) =>
        join(decls.map(doc(_)), hardline ~ hardline)

      case error: Error =>
        val info = error.info.toList.map(value => str(value.toString))
        Group(text("error") ~~ str(error.msg) ~ Nest(2, concat(info.map(line ~ _))))

  // top-level commands end without semicolon, also those that are not part of Dafny,
  // options and infos are named like attributes
  def doc(cmd: Cmd): Doc =
    cmd match
      case CheckSat =>
        text("check")

      case Labels =>
        text("labels")

      case GetModel =>
        text("model")

      case GetWitness =>
        text("witness")

      case Exit =>
        text("exit")

      case Done =>
        Error.raise("internal command cannot be printed", cmd)

      // the commands of SV-LIB have no counterpart
      case _: AnnotateTag | _: VerifyCall =>
        Error.raise("command not supported", cmd)

      case Push(depth) =>
        text("push") ~~ text(depth.toString)

      case Pop(depth) =>
        text("pop") ~~ text(depth.toString)

      case Reset =>
        text("reset")

      case SetLogic(name) =>
        text("logic") ~~ text(name)

      case GetOption(name) =>
        text("option") ~~ text(":" + name)

      case SetOption(name, value) =>
        Group(text("option") ~~ text(":" + name) ~~ text(":=") ~ Nest(2, line ~ any(value)))

      case GetInfo(name) =>
        text("info") ~~ text(":" + name)

      case SetInfo(name, value) =>
        Group(text("info") ~~ text(":" + name) ~~ text(":=") ~ Nest(2, line ~ any(value)))

      // the parameters of declared sorts are anonymous
      case DeclareSort(Con(name_, arity), attrs) =>
        text("type") ~ attributes(attrs) ~~ text(name(name_)) ~ params(Type.params("a", arity))

      case DefineSort(Con(name_, _), params_, body, attrs) =>
        text("type") ~ attributes(attrs) ~~ text(name(name_)) ~ params(params_) ~~ text("=") ~~ doc(body)

      // mutually recursive datatypes are declared one after another
      case DeclareDatatypes(cons, datas, attrs) =>
        val datas_ =
          for (con, data) <- cons zip datas
          yield datatype(con, data, attrs)

        join(datas_, hardline)

      case DeclareFun(Fun(name_, params_, Nil, res), attrs) =>
        header(text("const") ~ attributes(attrs) ~~ text(name(name_)) ~ params(params_) ~ text(":") ~~ doc(res), attrs, None)

      case DeclareFun(Fun(name_, params_, formals_, res), attrs) =>
        val sig = signature(name(name_), params_, formals_) ~ text(":") ~~ doc(res)
        header(text("function") ~ attributes(attrs) ~~ sig, attrs, None)

      case DefineFun(Fun(name_, params_, Nil, res), body, attrs) =>
        val head = text("const") ~ attributes(attrs) ~~ text(name(name_)) ~ params(params_) ~ text(":") ~~ doc(res)
        Group(head ~~ text(":=") ~ Nest(2, line ~ doc(body)))

      case DefineFun(Fun(name_, params_, formals_, res), body, attrs) =>
        val sig = signature(name(name_), params_, formals_) ~ text(":") ~~ doc(res)
        header(text("function") ~ attributes(attrs) ~~ sig, attrs, Some(braces(List(doc(body)))))

      // fuse g(f(xs), ys) = h, where h is ??? until the stage Fuse has processed it
      case FuseFuns(term, rhs, attrs) =>
        val rhs_ = rhs.map(doc(_)).getOrElse(text("???"))
        Group(text("fuse") ~ attributes(attrs) ~~ doc(term) ~~ text("=") ~ Nest(2, line ~ rhs_))

      // lemma name<a>(xs) returns (ys) requires φ ensures ψ for forall xs :: φ ==> exists ys :: ψ, named by :named,
      // the conjunctions are split into clauses; free lemmas have no body, the others the empty body
      case Assert(Lemma, params_, phi, attrs) =>
        val name_ = attrs.values[sexpr.Id]("named").map(_.text).headOption.getOrElse("unnamed")

        val (formals_, body) =
          phi match
            case All(formals_, body) => (formals_, body)
            case _                   => (Nil, phi)

        val (req, post) =
          body match
            case Imp(pre, post) => (And.flatten(pre), post)
            case _              => (Nil, body)

        val (rets, ens) =
          post match
            case Ex(rets, ens) => (rets, And.flatten(ens))
            case True          => (Nil, Nil)
            case _             => (Nil, And.flatten(post))

        val attrs_ = Attrs(attrs.attrs.filterNot((kw, _) => kw == "named" || kw == "free"))
        val clauses_ = Attrs(req.map("requires" -> Some(_)) ++ ens.map("ensures" -> Some(_)))
        val head = text("lemma") ~ attributes(attrs_) ~~ signature(name(name_), params_, formals_) ~ returns(rets)
        header(head, clauses_, if attrs.contains("free") then None else Some(braces(Nil)))

      // with type parameters, axiom <a> {:rw} forall x: a :: φ
      case Assert(justify, params_, phi, attrs) =>
        Group(text(format(justify)) ~ (if params_.isEmpty then empty else space ~ params(params_)) ~ attributes(attrs) ~ Nest(2, line ~ doc(phi)))

      // global variables are not Dafny, which has fields of objects instead
      case DeclareVar(Var(name_, typ), attrs) =>
        text("var") ~ attributes(attrs) ~~ text(name(name_)) ~ text(":") ~~ doc(typ)

      case DeclareProc(Proc(name_, params_, in, out), attrs) =>
        header(text("method") ~ attributes(attrs) ~~ signature(name(name_), params_, in) ~ returns(out), attrs, None)

      case DefineProc(Proc(name_, params_, in, out), body, attrs) =>
        header(text("method") ~ attributes(attrs) ~~ signature(name(name_), params_, in) ~ returns(out), attrs, Some(block(body)))

  // goals are not part of Dafny, they are printed like axioms with their own keyword
  def format(justify: Justify) =
    justify match
      case Axiom => "axiom"
      case Goal  => "goal"
      case Lemma => "lemma"

  // names A, B, C, ... for the parameters of declared sorts
  def params(params: List[Param]): Doc =
    if params.isEmpty
    then empty
    else text("<") ~ join(params.map(doc(_)), text(",") ~ space) ~ text(">")

  // the name of a function or method with its type parameters and formal parameters
  // the formal parameters flow up to the width of the line, aligned after the opening parenthesis
  def signature(name: String, params_ : List[Param], formals_ : List[Var]): Doc =
    text(name) ~ params(params_) ~ text("(") ~ flow(formals_.map(formal)) ~ text(")")

  def returns(out: List[Var]): Doc =
    if out.isEmpty
    then empty
    else space ~ text("returns (") ~ flow(out.map(formal)) ~ text(")")

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
          yield text(selector(con, sel) + ":") ~~ doc(sel.res)

        if sels.isEmpty
        then text(name(constr.name))
        else call(name(constr.name), sels_)

    // the = always goes on the next line, the constructors stay on its line if they fit, aligned by | otherwise
    val head = text("datatype") ~ attributes(attrs) ~~ text(name(con.name)) ~ params(params_)
    head ~ Nest(2, hardline ~ Group(text("=") ~~ join(constrs_, line ~ text("| "))))

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
        Group(text("{:" + name) ~ Nest(2, line ~ any(arg)) ~ text("}"))

  // the remaining attributes, each preceded by a space, written after the keyword of a declaration
  def attributes(attrs: Attrs): Doc =
    val attrs_ =
      for (name, arg) <- attrs.attrs if !isClause(name, arg)
      yield space ~ attribute(name, arg)

    concat(attrs_)

  // the components of a lexicographic termination measure are combined into a single clause
  def clauses(attrs: Attrs): List[Doc] =
    val clauses_ =
      for case (name, Some(arg)) <- attrs.attrs if isClause(name, Some(arg)) && name != "decreases"
      yield Group(text(name) ~ Nest(2, line ~ any(arg)))

    val dec = attrs.decreases

    if dec.isEmpty
    then clauses_
    else clauses_ :+ Group(text("decreases") ~ Nest(2, line ~ commas(dec.map(doc(_)))))

  // a declaration or loop followed by its contract clauses on separate lines,
  // the body starts on the same line only if there are no clauses
  def header(head: Doc, attrs: Attrs, body: Option[Doc]): Doc =
    val clauses_ = clauses(attrs)
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

  // the statements of a block, local variables are declared first
  def statements(prog: Prog): List[Doc] =
    prog match
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
        Group(text("assume") ~ Nest(2, line ~ doc(phi))) ~ text(";")

      case Spec(Nil, phi, True) =>
        Group(text("assert") ~ Nest(2, line ~ doc(phi))) ~ text(";")

      case Spec(xs, True, True) =>
        Group(commas(xs.map(doc(_))) ~~ text(":=") ~ Nest(2, line ~ commas(xs.map(_ => text("*"))))) ~ text(";")

      case Spec(xs, pre, post) =>
        val head = if xs.isEmpty then text("spec") else text("spec") ~~ commas(xs.map(doc(_)))
        val pre_ = Group(text("requires") ~ Nest(2, line ~ doc(pre)))
        val post_ = Group(text("ensures") ~ Nest(2, line ~ doc(post)))
        Group(head ~ Nest(2, line ~ pre_ ~ line ~ post_)) ~ text(";")

      case Assign(lhs, rhs) =>
        Group(commas(lhs.map(doc(_))) ~~ text(":=") ~ Nest(2, line ~ commas(rhs.map(doc(_))))) ~ text(";")

      case Call(proc, args, Nil) =>
        call(name(proc), args.map(doc(_))) ~ text(";")

      case Call(proc, args, res) =>
        Group(commas(res.map(doc(_))) ~~ text(":=") ~~ call(name(proc), args.map(doc(_)))) ~ text(";")

      case Block(_, _, _) =>
        block(prog)

      case Choice(Nil) =>
        text("assume false;")

      case Choice(List(prog)) =>
        doc(prog)

      case Choice(progs) =>
        val branches = progs.init.map(text("if *") ~~ block(_)) :+ block(progs.last)
        join(branches, text(" else "))

      case If(test, left, `skip`) =>
        text("if") ~~ doc(test) ~~ block(left)

      // else if chains
      case If(test, left, right: If) =>
        text("if") ~~ doc(test) ~~ block(left) ~~ text("else") ~~ doc(right)

      case If(test, left, right) =>
        text("if") ~~ doc(test) ~~ block(left) ~~ text("else") ~~ block(right)

      case While(test, body, attrs) =>
        header(text("while") ~ attributes(attrs) ~~ doc(test), attrs, Some(block(body)))

      case Iter(body, attrs) =>
        header(text("while") ~ attributes(attrs) ~~ text("*"), attrs, Some(block(body)))

      // the evolution constraint follows the keyword while
      case Ode(time, xs, rhs, dom, attrs) =>
        val lhs_ = text("ode") ~~ text(name(time.name)) ~~ text("::") ~~ commas(xs.map(x => text(name(x.name) + "'")))
        val rhs_ = commas(rhs.map(doc(_)))
        val dom_ = if dom == True then Nil else List(line ~ text("while") ~~ doc(dom))
        val ode = Group(lhs_ ~~ text("==") ~ Nest(2, line ~ rhs_ ~ concat(dom_)))
        header(ode, attrs, None) ~ text(";")

      case Par(progs) =>
        text("parallel {") ~ Nest(2, concat(progs.map(hardline ~ doc(_)))) ~ hardline ~ text("}")

  // the tuple types and their constructors, which are declared in the prelude as tuple₂, tuple₃, ...
  def isTuple(name: Name, arity: Int): Boolean =
    arity >= 2 && name == Name("tuple", Some(arity))

  def isTupleType(typ: Type): Boolean =
    typ match
      case Sort(Con(name_, arity), _) => isTuple(name_, arity)
      case _                          => false

  // types are not broken across lines
  def doc(typ: Type): Doc =
    typ match
      case Sort(Con(name_, arity), args) if isTuple(name_, arity) =>
        text("(") ~ join(args.map(doc(_)), text(",") ~ space) ~ text(")")

      // the arguments of a function type are parenthesized unless there is a single one that is no function or tuple,
      // e.g. int -> int, (int, bool) -> int, (int -> int) -> int, ((int, bool)) -> int
      case Arrow(List(arg), res) if Arrow.unapply(arg).isEmpty && !isTupleType(arg) =>
        doc(arg) ~~ text("->") ~~ doc(res)

      case Arrow(args, res) =>
        text("(") ~ join(args.map(doc(_)), text(",") ~ space) ~ text(")") ~~ text("->") ~~ doc(res)

      case BitVec(n) =>
        text("bv" + n)

      case Param(name_) =>
        text(name(name_))

      case Sort(Con(name_, _), Nil) =>
        text(name(name_))

      case Sort(Con(name_, _), args) =>
        text(name(name_)) ~ text("<") ~ join(args.map(doc(_)), text(",") ~ space) ~ text(">")

  def formal(x: Var): Doc =
    text(name(x.name) + ":") ~~ doc(x.typ)

  def formals(vars: List[Var]): Doc =
    commas(vars.map(formal))

  // the precedence of an expression in mixfix notation, and the associativity of its operator,
  // atoms bind tightest, binders, let and if-then-else extend as far to the right as possible
  val atomic = Int.MaxValue
  val lowest = -1

  // the bases of array accesses are atoms
  val operand = (atomic - 1, None)

  // the functions on bitvectors that implement operators of Dafny (see Overload.bitvectors),
  // as applications of these operators
  object bitvector:
    val ops =
      for ((op, arity), fun) <- Overload.bitvectors
      yield (fun, arity) -> op

    def unapply(expr: Expr): Option[App] =
      expr match
        case App(fun, inst, typ, args) if fun.name.index.isEmpty =>
          for op <- ops.get((fun.name.name, args.length))
          yield App(fun.copy(name = op), inst, typ, args)

        case _ =>
          None

  // the conversions between integers and bitvectors (see Overload.conversion), which are printed as e as T
  object conversion:
    def unapply(expr: Expr): Option[Expr] =
      expr match
        case App(fun, _, _, List(arg)) if fun.name.index.isEmpty && converts(fun.name.name) => Some(arg)
        case _                                                                               => None

    def converts(name: String) =
      name == "bv2nat" || name.startsWith("_ int2bv ") || name.startsWith("_ zero_extend ")
        || (name.startsWith("_ extract ") && name.endsWith(" 0"))

  def prefix(expr: Expr): Option[(String, Int, Expr)] =
    expr match
      case bitvector(app) =>
        prefix(app)

      // a != b and x !in s, see infix
      case Not(Eq(_, _)) | Not(Sets.member(_, _)) | Not(FinMaps.member(_, _)) | Not(Seqs.contains(_, Seqs.unit(_))) =>
        None

      case App(fun, _, _, List(arg)) if Grammar.prefix_ops.contains(name(fun.name)) =>
        val op = name(fun.name)
        Some((op, Grammar.prefix_ops(op), arg))

      case _ =>
        None

  // chains with more than two arguments are printed as nested applications, a + b + c is (a + b) + c,
  // which is wrong for chainable relations, which are printed like function calls, e.g. ==(x, y, z);
  // the comparisons do not associate when printed, since one to the left of another one would begin a chain,
  // chained comparisons x < y <= z are conjunctions instead (see comparisons)
  def infix(expr: Expr): Option[(String, Assoc, Int, List[Expr])] =
    expr match
      // sequence, set, and multiset literals are atoms
      case _ if elems(expr).isDefined || members(expr).isDefined || multiset(expr).isDefined || pairs(expr).isDefined =>
        None

      case bitvector(app) =>
        infix(app)

      // concatenation and prefix of sequences are overloaded in Dafny, x in s is containment of [x]
      case Seqs.concat(left, right) =>
        infix(App(Fun.seq.concat.copy(name = Name("+", None)), Nil, Sort.bool, List(left, right)))

      case Seqs.prefixof(left, right) =>
        infix(App(Fun.seq.prefixof.copy(name = Name("<=", None)), Nil, Sort.bool, List(left, right)))

      case Seqs.contains(seq, Seqs.unit(elem)) =>
        operator("in", List(elem, seq))

      case Not(Seqs.contains(seq, Seqs.unit(elem))) =>
        operator("!in", List(elem, seq))

      case Seqs.member(elem, seq)      => operator("in", List(elem, seq))
      case Not(Seqs.member(elem, seq)) => operator("!in", List(elem, seq))
      case Seqs.proper(left, right)    => operator("<", List(left, right))

      // the operations on sets and multisets are overloaded as well
      case Sets.member(elem, set)       => operator("in", List(elem, set))
      case Not(Sets.member(elem, set))  => operator("!in", List(elem, set))
      case Sets.union(left, right)      => operator("+", List(left, right))
      case Sets.inter(left, right)      => operator("*", List(left, right))
      case Sets.minus(left, right)      => operator("-", List(left, right))
      case Sets.subset(left, right)     => operator("<=", List(left, right))
      case Sets.proper(left, right)     => operator("<", List(left, right))
      case Bags.member(elem, bag)       => operator("in", List(elem, bag))
      case Not(Bags.member(elem, bag))  => operator("!in", List(elem, bag))
      case Bags.union(left, right)      => operator("+", List(left, right))
      case Bags.inter(left, right)      => operator("*", List(left, right))
      case Bags.minus(left, right)      => operator("-", List(left, right))
      case Bags.subbag(left, right)     => operator("<=", List(left, right))
      case Bags.proper(left, right)     => operator("<", List(left, right))

      // the update m[k := v] of a map is printed as an access, see doc
      case FinMaps.update(_, FinMaps.singleton(_, _)) => None
      case FinMaps.store(_, _, _)                     => None
      case FinMaps.member(key, map)                   => operator("in", List(key, map))
      case Not(FinMaps.member(key, map))              => operator("!in", List(key, map))
      case FinMaps.update(left, right)                => operator("+", List(left, right))
      case FinMaps.minus(left, right)                 => operator("-", List(left, right))
      // submaps, which this dialect adds to Dafny, without a strict version
      case FinMaps.subset(left, right)                => operator("<=", List(left, right))

      case App(fun, _, _, args) if Grammar.infix_ops.contains(name(fun.name)) =>
        val op = name(fun.name)
        val (assoc, prec) = Grammar.infix_ops(op)
        val chain = assoc != Assoc.Non && op != "!=" && !Grammar.chainable(op)
        if args.length == 2 || (args.length > 2 && chain)
        then operator(op, args)
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

  // an infix operator of Dafny applied to `args`
  def operator(op: String, args: List[Expr]): Option[(String, Assoc, Int, List[Expr])] =
    val (assoc, prec) = Grammar.infix_ops(op)
    Some((op, if Grammar.chainable(op) then Assoc.Non else assoc, prec, args))

  // a comparison x < y, which can be part of a chain
  def comparison(expr: Expr): Option[(String, Expr, Expr)] =
    infix(expr) match
      case Some((op, _, _, List(left, right))) if Grammar.chainable(op) => Some((op, left, right))
      case _                                                            => None

  // whether the comparisons `ops` go in one direction, which chains must not mix
  def monotone(ops: List[String]): Boolean =
    !(ops.exists(Set("<", "<=")) && ops.exists(Set(">", ">=")))

  // a conjunction x < y && y <= z of comparisons that are linked by their operands, printed as x < y <= z
  def comparisons(expr: Expr): Option[(List[String], List[Expr])] =
    expr match
      case And(phis) if phis.length >= 2 =>
        val cmps = phis.map(comparison)
        if cmps.forall(_.isDefined)
        then
          val cmps_ = cmps.flatten
          val ops = cmps_.map(_._1)
          val linked = cmps_.zip(cmps_.tail).forall { case ((_, _, right), (_, left, _)) => right == left }
          if linked && monotone(ops)
          then Some((ops, cmps_.head._2 :: cmps_.map(_._3)))
          else None
        else None

      case _ =>
        None

  // the maximal groups of consecutive conjuncts that can be printed as chained comparisons, which are conjunctions
  def chains(phis: List[Expr]): List[Expr] =
    val groups =
      phis.foldLeft(List[List[Expr]]()):
        case (group :: groups, phi) if comparisons(And(group.reverse :+ phi)).isDefined =>
          (phi :: group) :: groups
        case (groups, phi) =>
          List(phi) :: groups
    groups.reverse.map(group => And(group.reverse))

  // the elements of set literals, {}, {a}, and unions of these
  def members(expr: Expr): Option[List[Expr]] =
    expr match
      case Sets.empty()          => Some(Nil)
      case Sets.singleton(elem)  => Some(List(elem))
      case Sets.union(left, right) =>
        for left_ <- members(left); right_ <- members(right)
        yield left_ ++ right_
      case _ => None

  // the elements of multiset literals, multiset{}, multiset{a}, and unions of these
  def multiset(expr: Expr): Option[List[Expr]] =
    expr match
      case Bags.empty()                   => Some(Nil)
      case Bags.make(elem, Ints.one)       => Some(List(elem))
      case Bags.union(left, right) =>
        for left_ <- multiset(left); right_ <- multiset(right)
        yield left_ ++ right_
      case _ => None

  // the pairs of map literals, map[], map[k := v], and updates of these
  def pairs(expr: Expr): Option[List[(Expr, Expr)]] =
    expr match
      case FinMaps.empty()                => Some(Nil)
      case FinMaps.singleton(key, value)  => Some(List((key, value)))
      case FinMaps.update(left, right) =>
        for left_ <- pairs(left); right_ <- pairs(right)
        yield left_ ++ right_
      case _ => None

  // the elements of sequence literals, [], [a], and concatenations of these
  def elems(expr: Expr): Option[List[Expr]] =
    expr match
      case Seqs.empty() =>
        Some(Nil)

      case Seqs.unit(elem) =>
        Some(List(elem))

      case Seqs.concat(left, right) =>
        for left_ <- elems(left); right_ <- elems(right)
        yield left_ ++ right_

      case _ =>
        None

  def level(expr: Expr): (Int, Option[Assoc]) =
    expr match
      // binds tighter than all operators, but is not an operand of accesses
      case As(_, _) | conversion(_) =>
        (atomic - 1, None)

      case Lit(value: BigInt, _) if value < 0 =>
        (Grammar.prefix_ops("-"), None)

      // fractions n.0 / d.0, whose sign is part of the numerator
      case Lit(value: Rational, _) if value.den != 1 && (if value.isNegative then -value else value).decimal.isEmpty =>
        val (assoc, prec) = Grammar.infix_ops("/")
        (prec, Some(assoc))

      case Lit(value: Rational, _) if value.isNegative =>
        (Grammar.prefix_ops("-"), None)

      case Ite(_, _, _) | Bind(_, _, _) | Lam(_, _, _) | Let(_, _, _) | Match(_, _) =>
        (lowest, None)

      case _ =>
        prefix(expr) match
          case Some((_, prec, _)) =>
            (prec, None)

          case None if comparisons(expr).isDefined =>
            (Grammar.infix_ops("<")._2, Some(Assoc.Non))

          case None =>
            infix(expr) match
              case Some((_, assoc, prec, _)) =>
                (prec, Some(assoc))
              case None =>
                (atomic, None)

  // the wildcards _ of patterns are named apart by indices (see Parser), which are not printed
  def pattern(pat: Expr): Doc =
    pat match
      case Var(Name("_", Some(_)), _) =>
        text("_")

      // tuples of patterns, e.g. of a match on several values
      case Tuples(args) if args.length > 1 =>
        text("(") ~ commas(args.map(pattern)) ~ text(")")

      case App(fun, _, _, args) if args.nonEmpty =>
        text(name(fun.name)) ~ text("(") ~ commas(args.map(pattern)) ~ text(")")

      case _ =>
        doc(pat)

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

  // a combinator, whose head is followed by the dependencies after for, the keyword with the bound variables,
  // and the update, a single expression or guarded cases, case guard => result ...;
  // if it does not fit, the keyword goes below for and the update below the keyword, indented
  def combinator(head: Doc, deps: List[Expr], keyword: String, bound: List[Var], update: Expr): Doc =
    val updates_ =
      update match
        case Eps(updates) =>
          // a match as a result would take the following cases
          val cases =
            for Upd(cond, rhs) <- updates
            yield rhs match
              case Match(_, _) => text("case") ~~ doc(cond) ~~ text("=>") ~~ text("(") ~ Align(doc(rhs)) ~ text(")")
              case _           => text("case") ~~ doc(cond) ~~ text("=>") ~~ doc(rhs)
          Group(cases.reduce(_ ~ line ~ _))

        case _ =>
          doc(update)

    // the bound variables are never broken across lines
    val binders = text(bound.map(x => name(x.name)).mkString(", ") + " ::")
    val body = text("for") ~~ dependencies(deps) ~ line ~ text(keyword) ~~ binders ~ Nest(2, line ~ updates_)
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
      case Lit(value: Rational, typ) if value.isNegative =>
        (-value).decimal match
          case Some(digits) => text("-" + digits)
          case None         => text("-") ~ doc(Lit(-value, typ))

      case Lit(value: Rational, typ) =>
        value.decimal match
          case Some(digits) => text(digits)
          case None         => doc(Lit(Rational(value.num), typ)) ~~ text("/") ~~ doc(Lit(Rational(value.den), typ))

      case Lit(value, _) =>
        Error.raise("unprintable literal", expr)

      case Ite(test, left, right) =>
        Group(text("if") ~~ doc(test) ~ line ~ text("then") ~~ doc(left) ~ line ~ text("else") ~~ doc(right))

      // like the alternatives of Dafny's if statement, if { case p => x case q => y },
      // which is delimited by the braces and never parenthesized
      case Eps(updates) =>
        val cases =
          for Upd(cond, rhs) <- updates
          yield line ~ text("case") ~~ doc(cond) ~~ text("=>") ~~ doc(rhs)
        Group(text("if {") ~ Nest(2, concat(cases)) ~ line ~ text("}"))

      case _ if elems(expr).isDefined =>
        val Some(elems_) = elems(expr): @unchecked
        Group(text("[") ~ Nest(2, linebreak ~ commas(elems_.map(doc(_)))) ~ text("]"))

      case _ if members(expr).isDefined =>
        val Some(elems_) = members(expr): @unchecked
        Group(text("{") ~ Nest(2, linebreak ~ commas(elems_.map(doc(_)))) ~ text("}"))

      case _ if multiset(expr).isDefined =>
        val Some(elems_) = multiset(expr): @unchecked
        Group(text("multiset{") ~ Nest(2, linebreak ~ commas(elems_.map(doc(_)))) ~ text("}"))

      case _ if pairs(expr).isDefined =>
        val Some(pairs_) = pairs(expr): @unchecked
        val docs = for (key, value) <- pairs_ yield doc(key) ~~ text(":=") ~~ doc(value)
        Group(text("map[") ~ Nest(2, linebreak ~ commas(docs)) ~ text("]"))

      case FinMaps.card(arg) =>
        text("|") ~ doc(arg) ~ text("|")

      case FinMaps.get(map, key) =>
        doc(map, operand) ~ text("[") ~ doc(key) ~ text("]")

      case FinMaps.update(map, FinMaps.singleton(key, value)) =>
        Group(doc(map, operand) ~ text("[") ~ Nest(2, linebreak ~ doc(key) ~~ text(":=") ~ line ~ doc(value)) ~ text("]"))

      case FinMaps.store(map, key, value) =>
        Group(doc(map, operand) ~ text("[") ~ Nest(2, linebreak ~ doc(key) ~~ text(":=") ~ line ~ doc(value)) ~ text("]"))

      case FinMaps.keys(map) =>
        doc(map, operand) ~ text(".Keys")

      case FinMaps.values(map) =>
        doc(map, operand) ~ text(".Values")

      case Seqs.len(arg) =>
        text("|") ~ doc(arg) ~ text("|")

      case Sets.card(arg) =>
        text("|") ~ doc(arg) ~ text("|")

      case Bags.card(arg) =>
        text("|") ~ doc(arg) ~ text("|")

      // the multiplicity of an element of a multiset
      case Bags.count(elem, bag) =>
        doc(bag, operand) ~ text("[") ~ doc(elem) ~ text("]")

      case Bags.select(bag, elem) =>
        doc(bag, operand) ~ text("[") ~ doc(elem) ~ text("]")

      case Seqs.nth(seq, index) =>
        doc(seq, operand) ~ text("[") ~ doc(index) ~ text("]")

      case Seqs.update(seq, index, Seqs.unit(value)) =>
        Group(doc(seq, operand) ~ text("[") ~ Nest(2, linebreak ~ doc(index) ~~ text(":=") ~ line ~ doc(value)) ~ text("]"))

      case Seqs.store(seq, index, value) =>
        Group(doc(seq, operand) ~ text("[") ~ Nest(2, linebreak ~ doc(index) ~~ text(":=") ~ line ~ doc(value)) ~ text("]"))

      // the length is the difference of the bounds, s[i..j] is extract(s, i, j - i)
      case Seqs.extract(seq, from, len) =>
        val to = len match
          case Ints.minus(to, `from`)       => to
          case _ if from == Lit(BigInt(0), Sort.int) => len
          case _                           => Ints.plus(from, len)
        doc(seq, operand) ~ text("[") ~ doc(from) ~ text("..") ~ doc(to) ~ text("]")

      case App(fun, _, _, _) if (Fun.seq.all contains fun) && infix(expr).isEmpty =>
        Error.raise("not supported in Dafny", expr)

      case conversion(arg) =>
        doc(arg, operand) ~~ text("as") ~~ doc(expr.typ)

      case Select(base, index) =>
        doc(base, operand) ~ text("[") ~ doc(index) ~ text("]")

      case Store(base, index, value) =>
        Group(doc(base, operand) ~ text("[") ~ Nest(2, linebreak ~ doc(index) ~~ text(":=") ~ line ~ doc(value)) ~ text("]"))

      case _ if prefix(expr).isDefined =>
        val Some((op, prec, arg)) = prefix(expr): @unchecked
        text(op) ~ doc(arg, (prec, None))

      // x < y <= z, which breaks before the operators if it does not fit
      case _ if comparisons(expr).isDefined =>
        val Some((ops, args)) = comparisons(expr): @unchecked
        val inner = (Grammar.infix_ops("<")._2, None)
        val args_ = args.map(doc(_, inner))
        Group(args_.head ~ Nest(2, concat(ops.zip(args_.tail).map((op, arg) => line ~ text(op) ~~ arg))))

      // a op b op c, which breaks before the operators if it does not fit,
      // consecutive comparisons of conjunctions are chained, x < y <= z && b
      case _ if infix(expr).isDefined =>
        val Some((op, assoc, prec, args__)) = infix(expr): @unchecked
        val args_chained = chain(op, assoc, args__)
        val args = if op == "&&" then chains(args_chained) else args_chained
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

      case App(fun, _, _, args) if isTuple(fun.name, args.length) =>
        call("", args.map(doc(_)))

      // applications of function values, as calls of variables and constants, otherwise of the parenthesized value
      case Apply(f @ (_: Var | App(_, _, _, Nil)), args) =>
        doc(f) ~ text("(") ~ flow(args.map(doc(_))) ~ text(")")

      case Apply(f, args) =>
        text("(") ~ Align(doc(f)) ~ text(")") ~ text("(") ~ flow(args.map(doc(_))) ~ text(")")

      case App(fun, _, _, args) =>
        call(name(fun.name), args.map(doc(_)))

      // two or more arguments are printed in infix notation above
      case Distinct(_) =>
        Error.raise("unprintable distinct", expr)

      // the combinators of trace equation systems
      case Trace(init, deps, acc, bound, update) =>
        combinator(text("trace(") ~ doc(init) ~ text(",") ~ space, deps, "do", acc :: bound, update)

      case Maps(deps, bound, update) =>
        combinator(text("maps("), deps, "yield", bound, update)

      case Invs(deps, bound, body) =>
        combinator(text("invs("), deps, "check", bound, body)

      case Old(arg) =>
        call("old", List(doc(arg)))

      case Diff(xs, arg) =>
        Group(text("(") ~ Align(commas(xs.map(doc(_))) ~~ text("::") ~ Nest(2, line ~ doc(arg))) ~ text(")'"))

      // testers are parsed on variables only
      case Is(x: Var, fun) =>
        doc(x) ~ text("." + name(fun.name) + "?")

      case Is(_, _) =>
        Error.raise("tester on an expression that is not a variable not supported in Dafny", expr)

      case As(arg, typ) =>
        doc(arg, operand) ~~ text("as") ~~ doc(typ)

      // the variables of lambdas are annotated with their types, the body extends as far as possible
      case Lam(bound, body, Arrow(_, _)) =>
        Group(text("(") ~ flow(bound.map(formal)) ~ text(")") ~~ text("=>") ~ Nest(2, line ~ doc(body)))

      // the lambdas of SMT-LIB are arrays, which Dafny has no syntax for
      case Lam(_, _, _) =>
        Error.raise("lambda of array type not supported in Dafny", expr)

      // recursive functions are internal, printed for fuse only, like a function with a match whose cases are
      // patterns of all arguments with guards, function h(x: T): R { case h(p) if φ => e ... }, which is not parsed;
      // unambiguous, since function begins no expression, and case begins no body of a definition
      case Rec(Fun(name_, params_, formals_, res), cases) =>
        val cases_ =
          for Case(pat, body, cond) <- cases
          yield
            val guard = if cond == True then empty else space ~ text("if") ~~ doc(cond)
            Group(text("case") ~~ doc(pat) ~ guard ~~ text("=>") ~ Nest(2, line ~ doc(body)))

        val sig = signature(name(name_), params_, formals_) ~ text(":") ~~ doc(res)
        Group(text("function") ~~ sig ~~ text("{") ~ Nest(2, concat(cases_.map(line ~ _))) ~ line ~ text("}"))

      case Bind(quant, bound, body) =>
        // the bound variables flow up to the width of the line, aligned after the quantifier
        Group(text(name(quant)) ~~ flow(bound.map(formal)) ~~ text("::") ~ Nest(2, line ~ doc(body)))

      // the bodies of all but the last case are parenthesized if they would extend over the following cases
      case Match(arg, cases) =>
        Error.report("match with conditions not supported in Dafny", expr):
          require(cases.forall(_.cond == True))

        // a match on a tuple whose cases are tuples of patterns is a match on several values, match x, y case p, q
        val tuples =
          arg match
            case Tuples(args) => cases.forall { case Case(Tuples(pats), _, _) => pats.length == args.length; case _ => false }
            case _           => false

        val arg_ =
          arg match
            case Tuples(args) if tuples => Group(commas(args.map(doc(_))))
            case _                     => doc(arg)

        val cases_ =
          for (Case(pat, body, _), i) <- cases.zipWithIndex
          yield
            val pat_ =
              pat match
                case Tuples(pats) if tuples => Group(commas(pats.map(pattern)))
                case _                     => pattern(pat)
            val body_ = if i < cases.length - 1 then doc(body, (lowest, None)) else doc(body)
            Group(text("case") ~~ pat_ ~~ text("=>") ~ Nest(2, line ~ body_))

        Group(text("match") ~~ arg_ ~ Nest(2, concat(cases_.map(line ~ _))))

      case Let(bound, args, body) =>
        Group(text("var") ~~ formals(bound) ~~ text(":=") ~~ commas(args.map(doc(_))) ~ text(";") ~ line ~ doc(body))
