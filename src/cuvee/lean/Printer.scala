package cuvee.lean

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

// the logic in Lean 4: sorts, datatypes, functions and their definitions, axioms, lemmas, and goals,
// but no programs, procedures, or global variables, which are rejected; the output assumes `open Classical`
// (conditionals on propositions) and Mathlib for ℝ and Set;
// booleans are propositions, arrays are functions, sequences are lists, tuples are products,
// the built-in sorts and functions of the input languages are known to Lean (see Config.Lang.lean),
// those without a counterpart are rejected, e.g. multisets, finite maps, and bitvectors;
// traces and their combinators are the definitions of resources/cuvee/teq.lean
object Printer extends cuvee.pipe.Printer:

  // the keywords of Lean, which are escaped as names
  val keywords =
    Set("at", "by", "do", "else", "end", "for", "from", "fun", "have", "if", "in", "let", "match", "mut", "namespace",
      "open", "section", "show", "then", "theorem", "def", "axiom", "example", "where", "with", "structure", "class",
      "instance", "inductive", "mutual", "variable", "universe", "import", "deriving", "abbrev", "Type", "Prop", "Sort",
      "forall", "exists", "λ", "Π", "Σ", "true", "false", "prefix", "infix", "infixl", "infixr", "postfix", "notation",
      "macro", "syntax", "private", "protected", "partial", "unsafe", "calc", "suffices", "obtain", "local", "scoped",
      "attribute", "opaque", "nonrec", "noncomputable", "termination_by", "decreasing_by", "using", "namespace")

  // identifiers of Lean, which admit unicode letters and subscripts
  val identifier = "[a-zA-Z_\\p{L}][a-zA-Z0-9_'!?\\p{L}₀-₉]*".r

  // indexed names are printed with the index as unicode subscript, e.g. a₃,
  // other names are escaped by «», e.g. operators that are not built in
  def name(name: Name): String =
    val name_ = name.subscripted
    if identifier.matches(name_) && !keywords.contains(name_)
    then name_
    else "«" + name_ + "»"

  // type parameters a, b, c, ... are Greek letters α, β, γ, ..., such that they differ from the names of variables,
  // which Lean requires, e.g. of an array a: array<a, b>
  def param(param: Param): String =
    val greek = Map("a" -> "α", "b" -> "β", "c" -> "γ", "d" -> "δ", "e" -> "ε")
    greek.get(param.name.name) match
      case Some(letter) => name(param.name.copy(name = letter))
      case None         => name(param.name)

  def unsupported(what: Any): Nothing =
    Error.raise("not supported in Lean", what)

  // string literals escape backslashes and double quotes
  def str(value: String): Doc =
    text("\"" + util.Strings.escape(value) + "\"")

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
    unsupported(prog)

  // answers are comments
  def doc(res: Result): Doc =
    res match
      case Ack.Success    => text("-- success")
      case Ack.Unsupported => text("-- unsupported")
      case Ack.Done       => text("-- done")
      case Status.Unknown => text("-- unknown")
      case Status.Sat     => text("-- sat")
      case Status.Unsat   => text("-- unsat")
      case error: Error   => text("-- error " + error.msg + error.info.mkString(" ", " ", ""))
      case _              => text("-- " + res)

  // the type parameters of declarations are implicit
  def params(params: List[Param]): Doc =
    if params.isEmpty
    then empty
    else text(" {" + params.map(param).mkString(" ") + " : Type}")

  def binder(x: Var): Doc =
    text("(" + name(x.name) + " :") ~~ doc(x.typ) ~ text(")")

  // the binders of the formal parameters flow up to the width of the line
  def binders(xs: List[Var]): Doc =
    if xs.isEmpty
    then empty
    else space ~ Align(Doc.fill(xs.map(binder), empty))

  // the name of a declaration with its type parameters and formal parameters
  def signature(name_ : Name, params_ : List[Param], formals_ : List[Var]): Doc =
    text(name(name_)) ~ params(params_) ~ binders(formals_)

  // the type of a declared function, curried, → associates to the right
  def curried(args: List[Type], res: Type): Doc =
    join(args.map(doc(_, arrow + 1)) :+ doc(res, arrow), text(" →") ~ space)

  // the name of an assertion: its attribute :named, otherwise derived from the formula, since axioms need a name
  def named(attrs: Attrs, phi: Expr): String =
    attrs.values[sexpr.Id]("named").map(_.text).headOption match
      case Some(name_) => name(name_)
      case None        => "ax_" + Integer.toHexString(phi.hashCode)

  // the universally quantified variables of a formula become the binders of the declaration
  def statement(head: Doc, phi: Expr, proof: Option[Doc]): Doc =
    val (xs, body) =
      phi match
        case All(xs, body) => (xs, body)
        case _             => (Nil, phi)

    val decl = Group(head ~ Nest(4, binders(xs)) ~~ text(":") ~ Nest(2, line ~ doc(body)))
    proof match
      case None        => decl
      case Some(proof) => Group(decl ~~ text(":=") ~ Nest(2, line ~ proof))

  // rewrite rules of -simplify are simp lemmas
  def simp(attrs: Attrs): Doc =
    if attrs.contains("rw") then text("@[simp]") ~ space else empty

  // the commands of SMT-LIB that have no counterpart are comments
  def doc(cmd: Cmd): Doc =
    cmd match
      case CheckSat              => text("-- check-sat")
      case Labels                => text("-- labels")
      case GetModel              => text("-- get-model")
      case Exit                  => text("-- exit")
      case Push(depth)           => text("-- push " + depth)
      case Pop(depth)            => text("-- pop " + depth)
      case Reset                 => text("-- reset")
      case SetLogic(name)        => text("-- logic " + name)
      case GetOption(name)       => text("-- option :" + name)
      case SetOption(name, _)    => text("-- option :" + name)
      case GetInfo(name)         => text("-- info :" + name)
      case SetInfo(name, _)      => text("-- info :" + name)

      case Done =>
        Error.raise("internal command cannot be printed", cmd)

      // uninterpreted sorts are axiomatized types
      case DeclareSort(Con(name_, arity), _) =>
        text("axiom " + name(name_) + " :") ~~ text((List.fill(arity)("Type") :+ "Type").mkString(" → "))

      case DefineSort(Con(name_, _), params_, body, _) =>
        val params__ = if params_.isEmpty then empty else text(" (" + params_.map(param).mkString(" ") + " : Type)")
        text("abbrev " + name(name_)) ~ params__ ~~ text(":=") ~~ doc(body)

      // mutually recursive datatypes in a mutual block
      case DeclareDatatypes(cons, datas, _) =>
        val inductives = for (con, data) <- cons zip datas yield inductive(con, data)
        val sels = for (con, data) <- cons zip datas; sel <- selectors(con, data) yield sel
        val opens = for con <- cons yield text("open " + name(con.name))
        val block =
          if cons.length == 1
          then inductives.head
          else text("mutual") ~ Nest(2, concat(inductives.map(hardline ~ _))) ~ hardline ~ text("end")
        join(block :: opens ++ sels, hardline ~ hardline)

      case DeclareFun(Fun(name_, params_, Nil, res), _) =>
        text("axiom") ~~ text(name(name_)) ~ params(params_) ~~ text(":") ~~ doc(res)

      case DeclareFun(Fun(name_, params_, formals_, res), _) =>
        Group(text("axiom") ~~ text(name(name_)) ~ params(params_) ~~ text(":") ~ Nest(2, line ~ curried(formals_.types, res)))

      // definitions that use conditionals on propositions are not computable
      case DefineFun(Fun(name_, params_, formals_, res), body, _) =>
        val head = text("noncomputable def") ~~ signature(name_, params_, formals_) ~~ text(":") ~~ doc(res)
        Group(head ~~ text(":=") ~ Nest(2, line ~ doc(body)))

      // axioms and free lemmas are assumed, the other lemmas are theorems to be proved
      case Assert(Axiom, params_, phi, attrs) =>
        statement(simp(attrs) ~ text("axiom") ~~ text(named(attrs, phi)) ~ params(params_), phi, None)

      case Assert(Lemma, params_, phi, attrs) if attrs.contains("free") =>
        statement(simp(attrs) ~ text("axiom") ~~ text(named(attrs, phi)) ~ params(params_), phi, None)

      case Assert(Lemma, params_, phi, attrs) =>
        statement(simp(attrs) ~ text("theorem") ~~ text(named(attrs, phi)) ~ params(params_), phi, Some(text("by sorry")))

      // goals are anonymous
      case Assert(Goal, params_, phi, _) =>
        statement(text("example") ~ params(params_), phi, Some(text("by sorry")))

      case _: DeclareVar | _: DeclareProc | _: DefineProc | _: FuseFuns =>
        unsupported(cmd)

  // inductive T (a : Type) where | C (x : A) : T a, whose arguments are named after the selectors
  def inductive(con: Con, data: Datatype): Doc =
    val Datatype(params_, constrs) = data
    val sort = doc(Sort(con, params_))
    val params__ = if params_.isEmpty then empty else text(" (" + params_.map(param).mkString(" ") + " : Type)")

    val constrs_ =
      for (constr, sels) <- constrs
      yield
        val args = for sel <- sels yield text("(" + selector(con, sel) + " :") ~~ doc(sel.res) ~ text(")")
        text("| " + name(constr.name)) ~ concat(args.map(space ~ _)) ~~ text(":") ~~ sort

    text("inductive " + name(con.name)) ~ params__ ~~ text("where") ~ Nest(2, concat(constrs_.map(hardline ~ _)))

  // selectors are qualified with the datatype (see dafny.Parser.datatype), the arguments of constructors are not
  def selector(con: Con, sel: Fun): String =
    name(Name(sel.name.subscripted.stripPrefix(con.name.subscripted + "_"), None))

  // selectors are partial functions, axiomatized like in SMT-LIB by their values on their constructors
  def selectors(con: Con, data: Datatype): List[Doc] =
    val Datatype(params_, constrs) = data
    for
      (constr, sels) <- constrs
      sel <- sels
    yield
      // the arguments are named apart from the selectors, which are not qualified in SMT-LIB
      val xs = for (sel_, i) <- sels.zipWithIndex yield Var(Name("x", Some(i)), sel_.res)
      val x = xs(sels.indexOf(sel))
      val decl = text("axiom") ~~ text(name(sel.name)) ~ params(params_) ~~ text(":") ~~ curried(sel.args, sel.res)
      val eq = Eq(App(sel, Nil, sel.res, List(App(constr, Nil, sel.args.head, xs))), x)
      val head = text("axiom") ~~ text(name(Name(sel.name.subscripted + "_" + constr.name.subscripted, None))) ~ params(params_)
      decl ~ hardline ~ hardline ~ statement(head, All(xs, eq), None)

  // the tuple types and their constructors, which are declared in the prelude of Dafny as tuple₂, tuple₃, ...
  def isTuple(name: Name, arity: Int): Boolean =
    name == Name("tuple", Some(arity))

  // the selectors tupleₙ_i of the components of tuples
  object component:
    val pattern = "tuple([₀-₉]+)_([0-9]+)".r

    def unapply(expr: Expr): Option[(Expr, Int, Int)] =
      expr match
        case App(fun, _, _, List(arg)) if fun.name.index.isEmpty =>
          fun.name.name match
            case pattern(n, i) => Some((arg, n.map(c => (c - '₀' + '0').toChar).toInt, i.toInt))
            case _             => None
        case _ =>
          None

  // the precedences of Lean, see its notations; application binds tightest, binders extend as far as possible
  val max = 1024
  val arrow = 25
  val lowest = 0

  // the binary operators of the core with their notation in Lean, precedence, and associativity
  val infix_ops = Map(
    "<=>" -> ("↔", 20, Assoc.Non),
    "=>" -> ("→", 25, Assoc.Right),
    "or" -> ("∨", 30, Assoc.Right),
    "and" -> ("∧", 35, Assoc.Right),
    "=" -> ("=", 50, Assoc.Non),
    "<" -> ("<", 50, Assoc.Non),
    "<=" -> ("≤", 50, Assoc.Non),
    ">" -> (">", 50, Assoc.Non),
    ">=" -> ("≥", 50, Assoc.Non),
    "+" -> ("+", 65, Assoc.Left),
    "-" -> ("-", 65, Assoc.Left),
    "*" -> ("*", 70, Assoc.Left),
    "div" -> ("/", 70, Assoc.Left),
    "/" -> ("/", 70, Assoc.Left),
    "mod" -> ("%", 70, Assoc.Left)
  )

  // the infix operators of an expression with its arguments, chains of the associative ones flattened
  def infix(expr: Expr): Option[(String, Int, Assoc, List[Expr])] =
    expr match
      case Seqs.concat(left, right)    => Some(("++", 65, Assoc.Left, List(left, right)))
      case Sets.member(elem, set)      => Some(("∈", 50, Assoc.Non, List(elem, set)))
      case Not(Sets.member(elem, set)) => Some(("∉", 50, Assoc.Non, List(elem, set)))
      case Sets.union(left, right)     => Some(("∪", 65, Assoc.Left, List(left, right)))
      case Sets.inter(left, right)     => Some(("∩", 70, Assoc.Left, List(left, right)))
      case Sets.minus(left, right)     => Some(("\\", 70, Assoc.Left, List(left, right)))
      case Sets.subset(left, right)    => Some(("⊆", 50, Assoc.Non, List(left, right)))
      case Sets.proper(left, right)    => Some(("⊂", 50, Assoc.Non, List(left, right)))

      // equality of propositions is equivalence
      case Eq(left, right) if left.typ == Sort.bool => Some(("↔", 20, Assoc.Non, List(left, right)))
      case Not(Eq(left, right))                     => Some(("≠", 50, Assoc.Non, List(left, right)))
      case Distinct(List(left, right))              => Some(("≠", 50, Assoc.Non, List(left, right)))

      case App(fun, _, _, args @ (_ :: _ :: _)) if fun.name.index.isEmpty && infix_ops.contains(fun.name.name) =>
        val (op, prec, assoc) = infix_ops(fun.name.name)
        fun.name.name match
          case "and" => Some((op, prec, assoc, And.flatten(expr)))
          case "or"  => Some((op, prec, assoc, Or.flatten(expr)))
          case _ if args.length == 2 => Some((op, prec, assoc, args))
          case _ => None

      case _ =>
        None

  def prefix(expr: Expr): Option[(String, Int, Expr)] =
    expr match
      case Not(Sets.member(_, _)) | Not(Eq(_, _)) => None
      case Not(arg)                                => Some(("¬", 40, arg))
      case App(fun, _, _, List(arg)) if fun.name == Name("-", None) => Some(("-", 75, arg))
      case _                                       => None

  def level(expr: Expr): Int =
    expr match
      case Lit(value: BigInt, _) if value < 0               => 75
      case Lit(value: Rational, _) if value.isNegative      => 75
      case Lit(value: Rational, _) if value.decimal.isEmpty => 70
      case Ite(_, _, _) | Bind(_, _, _) | Lam(_, _, _) | Let(_, _, _) | Match(_, _) | Store(_, _, _) => lowest
      case Eps(updates) if updates.length > 1 => lowest
      case Trace(_, _, _, _, _) | Maps(_, _, _) | Invs(_, _, _) => max - 1
      case Seqs.len(_) | Seqs.unit(_) | Seqs.empty() | Sets.empty() | Sets.singleton(_) => max
      case Distinct(exprs) if exprs.length > 2              => 35
      case As(_, _) | Is(_, _)                              => max
      case _ if prefix(expr).isDefined                      => prefix(expr).get._2
      case _ if infix(expr).isDefined                       => infix(expr).get._2
      case Select(_, _) | Apply(_, _) | Seqs.nth(_, _) => max - 1
      case component(arg, n, _) if n > 1                    => max
      case App(_, _, _, _ :: _)                             => max - 1
      case _                                                => max

  // an expression in a context of at least the given precedence
  def doc(expr: Expr, min: Int): Doc =
    if level(expr) >= min
    then doc(expr)
    else text("(") ~ Align(doc(expr)) ~ text(")")

  // the arguments of applications, which must be atoms
  def arg(expr: Expr): Doc =
    doc(expr, max)

  def app(fun: Doc, args: List[Expr]): Doc =
    Group(fun ~ Nest(2, concat(args.map(line ~ arg(_)))))

  // literals and arithmetic on them, whose type is not determined by the context in Lean, e.g. Nat by default
  def numeral(expr: Expr): Boolean =
    expr match
      case Lit(_: BigInt, _) | Lit(_: Rational, _) => true
      case App(fun, _, _, args) if fun.name.index.isEmpty && Set("+", "-", "*", "div", "mod", "/").contains(fun.name.name) =>
        args.forall(numeral)
      case _ => false

  // a variable of type `typ` that occurs in none of `exprs`, for the argument of updated arrays
  def fresh(exprs: List[Expr], typ: Type): Var =
    val used = exprs.flatMap(_.free).map(_.name.subscripted).toSet
    val name_ = Iterator.from(0).map(i => if i == 0 then "j" else "j" + i).find(!used.contains(_)).get
    Var(Name(name_, None), typ)

  def doc(expr: Expr): Doc =
    expr match
      case Var(name_, _) =>
        text(name(name_))

      case True =>
        text("True")

      case False =>
        text("False")

      case Lit(value: BigInt, _) =>
        text(value.toString)

      case Lit(value: String, _) =>
        str(value)

      case Lit(value: Rational, typ) if value.isNegative =>
        text("-") ~ doc(Lit(-value, typ), 75)

      case Lit(value: Rational, typ) =>
        value.decimal match
          case Some(digits) => text(digits)
          case None         => text(value.num.toString) ~~ text("/") ~~ text(value.den.toString)

      case Lit(_, _) =>
        unsupported(expr)

      case Ite(test, left, right) =>
        Group(text("if") ~~ doc(test) ~~ text("then") ~ Nest(2, line ~ doc(left)) ~ line ~ text("else") ~ Nest(2, line ~ doc(right)))

      // arrays are functions, an update is the function that differs at the index
      case Select(base, index) =>
        app(doc(base, max - 1), List(index))

      case Store(base, index, value) =>
        val j = fresh(List(base, index, value), index.typ)
        val body = Ite(Eq(j, index), value, Select(base, j))
        Group(text("fun") ~~ text(name(j.name)) ~~ text("=>") ~ Nest(2, line ~ doc(body)))

      // sequences are lists, indexed by natural numbers
      case Seqs.empty() =>
        text("[]")

      case Seqs.unit(elem) =>
        text("[") ~ doc(elem) ~ text("]")

      case Seqs.len(seq) =>
        text("(") ~ doc(seq, max) ~ text(".length : Int)")

      case Seqs.nth(seq, index) =>
        app(doc(seq, max) ~ text(".getD"), Nil) ~~ text("(") ~ doc(index, max) ~ text(".toNat)") ~~ text("default")

      case Seqs.extract(seq, from, len) =>
        text("((") ~ doc(seq, max) ~ text(".drop ") ~ doc(from, max) ~ text(".toNat).take ") ~ doc(len, max) ~ text(".toNat)")

      case Seqs.store(seq, index, value) =>
        doc(seq, max) ~ text(".set ") ~ doc(index, max) ~ text(".toNat ") ~ arg(value)

      case App(fun, _, _, _) if Fun.seq.all.contains(fun) && infix(expr).isEmpty =>
        unsupported(expr)

      // sets are those of Mathlib
      case Sets.empty() =>
        text("∅")

      case Sets.singleton(elem) =>
        text("{") ~ doc(elem) ~ text("}")

      case App(fun, _, _, _) if Fun.set.all.contains(fun) && infix(expr).isEmpty =>
        unsupported(expr)

      case App(fun, _, _, _) if Fun.bag.all.contains(fun) || Fun.map.all.contains(fun) =>
        unsupported(expr)

      case App(fun, _, _, _) if fun.name.index.isEmpty && (BitVecs.names.contains(fun.name.name) || fun.name.name.startsWith("_ ")) =>
        unsupported(expr)

      case _ if prefix(expr).isDefined =>
        val Some((op, prec, arg_)) = prefix(expr): @unchecked
        text(op) ~ doc(arg_, prec)

      // a op b op c, which breaks before the operators if it does not fit;
      // the first operand of a comparison of numerals is annotated with its type, which Lean cannot infer otherwise
      case _ if infix(expr).isDefined =>
        val Some((op, prec, assoc, args)) = infix(expr): @unchecked
        val annotate = expr.typ == Sort.bool && args.forall(numeral)
        val args_ =
          for (arg_, i) <- args.zipWithIndex
          yield
            val min =
              assoc match
                case Assoc.Left if i == 0                => prec
                case Assoc.Right if i == args.length - 1 => prec
                case _                                   => prec + 1
            if annotate && i == 0
            then text("(") ~ doc(arg_) ~~ text(":") ~~ doc(arg_.typ) ~ text(")")
            else doc(arg_, min)
        Group(args_.head ~ Nest(2, concat(args_.tail.map(line ~ text(op) ~~ _))))

      // pairwise distinct
      case Distinct(exprs) =>
        val pairs = for case a :: rest <- exprs.tails.toList; b <- rest yield Not(Eq(a, b))
        doc(And(pairs))

      // tuples are nested pairs, (a, b, c) is (a, (b, c)), whose components are selected by .1 and .2
      case App(fun, _, _, List(arg_)) if isTuple(fun.name, 1) =>
        doc(arg_)

      case App(fun, _, _, args) if isTuple(fun.name, args.length) =>
        text("(") ~ Align(join(args.map(doc(_)), text(",") ~ line)) ~ text(")")

      case component(arg_, 1, _) =>
        doc(arg_)

      case component(arg_, n, i) =>
        val path = List.fill(i)(".2") ++ (if i < n - 1 then List(".1") else Nil)
        doc(arg_, max) ~ text(path.mkString)

      case App(fun, _, _, Nil) =>
        text(name(fun.name))

      case Apply(f, args) =>
        app(doc(f, max - 1), args)

      case App(fun, _, _, args) =>
        app(text(name(fun.name)), args)

      // a tester is a match on the constructor
      case Is(arg_, fun) =>
        text("(match") ~~ doc(arg_) ~~ text("with | ." + name(fun.name) + " .. => True | _ => False)")

      case As(arg_, typ) =>
        text("(") ~ doc(arg_) ~~ text(":") ~~ doc(typ) ~ text(")")

      // binders with typed variables, which flow up to the width of the line
      case Bind(quant, bound, body) =>
        val q = if quant == Name("forall", None) then "∀" else if quant == Name("exists", None) then "∃" else unsupported(expr)
        Group(text(q) ~ binders(bound) ~ text(",") ~ Nest(2, line ~ doc(body)))

      case Lam(bound, body, _) =>
        Group(text("fun") ~ binders(bound) ~~ text("=>") ~ Nest(2, line ~ doc(body)))

      // the variables of a let are bound in parallel, as a tuple if there are several, annotated with their types
      case Let(List(x), List(e), body) =>
        val head = text("let") ~~ text(name(x.name)) ~~ text(":") ~~ doc(x.typ) ~~ text(":=")
        Align(Group(head ~ Nest(2, line ~ doc(e))) ~ text(";") ~ line ~ doc(body))

      case Let(bound, args, body) =>
        val xs = text("(" + bound.map(x => name(x.name)).mkString(", ") + ") :") ~~ join(bound.map(x => doc(x.typ, 36)), text(" ×") ~ space)
        val es = text("(") ~ Align(join(args.map(doc(_)), text(",") ~ line)) ~ text(")")
        Align(Group(text("let") ~~ xs ~~ text(":=") ~ Nest(2, line ~ es)) ~ text(";") ~ line ~ doc(body))

      case Match(arg_, cases) =>
        Error.report("match with conditions not supported in Lean", expr):
          require(cases.forall(_.cond == True))

        val cases_ =
          for (Case(pat, body, _), i) <- cases.zipWithIndex
          yield
            val body_ = if i < cases.length - 1 then doc(body, lowest + 1) else doc(body)
            Group(text("|") ~~ pattern(pat) ~~ text("=>") ~ Nest(2, line ~ body_))

        Align(text("match") ~~ doc(arg_) ~~ text("with") ~ concat(cases_.map(hardline ~ _)))

      // the combinators of trace equation systems, as applications of the functions of teq.lean by the number of
      // their dependencies (trace, trace2, ...) to the dependencies and the update as a function of the bound variables
      case Trace(init, deps, acc, bound, update) =>
        combinator("trace", init :: deps, acc :: bound, update)

      case Maps(deps, bound, update) =>
        combinator("maps", deps, bound, update)

      case Invs(deps, bound, body) =>
        combinator("invs", deps, bound, body)

      // the guards of the cases of an update are disjoint and complete, the last one is implied by the others
      case Eps(updates) =>
        val Upd(_, last) = updates.last
        doc(updates.init.foldRight(last) { case (Upd(cond, rhs), rest) => Ite(cond, rhs, rest) })

      case _: Old | _: Diff | _: Rec =>
        unsupported(expr)

  def combinator(name_ : String, args: List[Expr], bound: List[Var], update: Expr): Doc =
    val deps = if name_ == "trace" then args.length - 1 else args.length
    val fun = Group(text("fun " + bound.map(x => name(x.name)).mkString(" ") + " =>") ~ Nest(2, line ~ doc(update)))
    val head = text(if deps == 1 then name_ else name_ + deps)
    Group(head ~ Nest(2, concat(args.map(line ~ arg(_))) ~ line ~ text("(") ~ Align(fun) ~ text(")")))

  // patterns of constructors, whose wildcards are named apart by indices (see dafny.Parser), which are not printed
  def pattern(pat: Expr): Doc =
    pat match
      case Var(Name("_", Some(_)), _) =>
        text("_")

      case App(fun, _, _, Nil) =>
        text("." + name(fun.name))

      case App(fun, _, _, args) =>
        val args_ =
          for arg <- args
          yield arg match
            case App(_, _, _, _ :: _) => text("(") ~ pattern(arg) ~ text(")")
            case _                    => pattern(arg)
        text("." + name(fun.name)) ~ concat(args_.map(space ~ _))

      case _ =>
        doc(pat)

  // types are not broken across lines
  def doc(typ: Type, min: Int): Doc =
    val prec =
      typ match
        case Arrow(_, _) | Sort(Con.array, _) => arrow
        case Sort(Con(name_, arity), args) if isTuple(name_, arity) && arity > 1 => 35
        case Sort(_, Nil) | Param(_)                                             => max
        case Sort(Con(name_, 1), _) if isTuple(name_, 1)                         => max
        case _                                                                   => max - 1

    if prec >= min
    then doc(typ)
    else text("(") ~ doc(typ) ~ text(")")

  def doc(typ: Type): Doc =
    typ match
      case Sort(Con.bool, Nil)   => text("Prop")
      case Sort(Con.int, Nil)    => text("Int")
      case Sort(Con.real, Nil)   => text("ℝ")
      case Sort(Con.string, Nil) => text("String")

      // arrays and function values are functions
      case Sort(Con.array, List(dom, ran)) =>
        doc(dom, arrow + 1) ~~ text("→") ~~ doc(ran, arrow)

      case Arrow(args, res) =>
        curried(args, res)

      case Sort(Con.seq, List(elem)) =>
        text("List") ~~ doc(elem, max)

      case Sort(Con.set, List(elem)) =>
        text("Set") ~~ doc(elem, max)

      case Sort(Con(name_, 1), List(elem)) if isTuple(name_, 1) =>
        doc(elem)

      case Sort(Con(name_, arity), args) if isTuple(name_, arity) =>
        join(args.map(doc(_, 36)), text(" ×") ~ space)

      case Sort(Con.bag | Con.map, _) =>
        unsupported(typ)

      case typ: Param =>
        text(param(typ))

      case Sort(Con(name_, _), Nil) =>
        text(name(name_))

      case Sort(Con(name_, _), args) =>
        text(name(name_)) ~ concat(args.map(arg => space ~ doc(arg, max)))
