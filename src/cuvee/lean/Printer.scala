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

import scala.collection.mutable

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
      case Status.Correct   => text("-- correct")
      case Status.Incorrect => text("-- incorrect")
      case error: Error   => text("-- error " + error.msg + error.info.mkString(" ", " ", ""))
      case _              => text("-- " + res)

  // the type parameters of declarations are implicit, each with an instance Inhabited, which the functions on traces
  // and lists need for the elements outside of them (unspecified, earlier, current), as in teq.lean
  def params(params: List[Param]): Doc =
    if params.isEmpty
    then empty
    else text(" {" + params.map(param).mkString(" ") + " : Type}") ~ concat(params.map(p => text(" [Inhabited " + param(p) + "]")))

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

  // the universally quantified variables of a formula become the binders of the declaration, followed by the further
  // variables `fresh` and the hypotheses `hyps` on the lengths of dependencies (see lengths);
  // the proof always starts on the line after :=, like the bodies of definitions
  def statement(head: Doc, phi: Expr, proof: Option[Doc], fresh: List[Var] = Nil, hyps: List[(String, Expr)] = Nil): Doc =
    val (xs, body) =
      phi match
        case All(xs, body) => (xs, body)
        case _             => (Nil, phi)

    // a hypothesis is not broken across lines
    val hyps_ = for (name_, hyp) <- hyps yield text("(" + name_ + " : " + render(doc(hyp), 1000).mkString(" ") + ")")
    val binders_ = (xs ++ fresh).map(binder) ++ hyps_
    val all = if binders_.isEmpty then empty else space ~ Align(Doc.fill(binders_, empty))
    val decl = Group(head ~ Nest(4, all) ~~ text(":") ~ Nest(2, line ~ doc(body)))
    proof match
      case None        => decl
      case Some(proof) => decl ~~ text(":=") ~ Nest(2, hardline ~ proof)

  // the hypotheses on the lengths of the dependencies of the combinators in a lemma, whose semantics in Lean zips the
  // dependencies, which truncates them to the shortest one, whereas the dependencies of a combinator of Cuvée have equal
  // lengths (see resources/cuvee/teq.lean): the lists among the dependencies of each combinator, also of a function
  // defined by one (:fold, e.g. stores), and the lists read at the iterations k of a counter, earlier(natural(k), xs),
  // have the length n of the loop, the number of steps of ⌊counter(_, _, n)⌋ or ⌊consts(n, _)⌋ among the dependencies,
  // or a fresh variable n of the lemma if no counter gives it; the hypotheses `length xs = n` use the function length
  // of teq.dfy, List.length of Lean, and are named h<xs>
  def lengths(phi: Expr): (List[Var], List[(String, Expr)]) =
    val (xs, body) =
      phi match
        case All(xs, body) => (xs, body)
        case _             => (Nil, phi)

    val tagged = dependencies(body, Map())
    val vars = tagged.map(_._1).distinct
    val known = tagged.collect { case (x, Some(n)) => (x, n) }.toMap

    val fresh =
      if vars.forall(known.contains) then None
      else
        val used = (body.free ++ xs).map(_.name.subscripted)
        val name_ = Iterator.from(0).map(i => if i == 0 then "n" else "n" + i).find(!used.contains(_)).get
        Some(Var(Name(name_, None), Sort.nat))

    val hyps = for x <- vars yield ("h" + name(x.name), Eq(App(length, List(x)), known.getOrElse(x, fresh.get)))
    (fresh.toList, hyps)

  // the function length of lists, List.length of Lean, declared in teq.dfy with :lean, hence not printed
  val length = Fun("length", List(Param("a")), List(Var("xs", Sort.list(Param("a")))), Sort.nat)

  // the positions of the formal parameters of the functions defined by a combinator (:fold, e.g. stores) that are
  // its dependencies, recorded when the definitions are printed
  val folds = mutable.Map[Name, List[Int]]()

  def positions(fun: Fun, body: Expr): List[Int] =
    val deps =
      body match
        case Trace(_, deps, _, _, _) => deps
        case Maps(deps, _, _)        => deps
        case Invs(deps, _, _)        => deps
        case _                       => Nil
    deps.collect { case x: Var if fun.formals.contains(x) => fun.formals.indexOf(x) }

  // the lists that are dependencies of combinators in `expr` with the lengths of their loops, if a counter gives them,
  // where `counters` are the variables bound to the iterations of counters by the enclosing combinators
  def dependencies(expr: Expr, counters: Map[Var, Expr]): List[(Var, Option[Expr])] =
    expr match
      case Trace(inits, deps, _, bound, results) =>
        inits.flatMap(dependencies(_, counters)) ++ results.flatMap(loop(deps, bound, _, counters))

      case Maps(deps, bound, update) =>
        loop(deps, bound, update, counters)

      case Invs(deps, bound, body) =>
        loop(deps, bound, body, counters)

      case Earlier(Nats.natural(k: Var), xs: Var) if counters.contains(k) =>
        List((xs, Some(counters(k))))

      case App(fun, _, _, args) if folds.contains(fun.name) =>
        tag(folds(fun.name).map(args)) ++ args.flatMap(dependencies(_, counters))

      case _ =>
        val buffer = mutable.ListBuffer[(Var, Option[Expr])]()
        expr.map { sub => buffer ++= dependencies(sub, counters); sub }
        buffer.toList

  // the number of steps of a counter among the dependencies, if any
  def steps(deps: List[Expr]): Option[Expr] =
    deps.collectFirst {
      case Butlast(Counter(_, _, n))                                                       => n
      case Butlast(App(fun, _, _, List(n, _))) if fun.name == Name("consts", None)         => n
    }

  def tag(deps: List[Expr]): List[(Var, Option[Expr])] =
    val n = steps(deps)
    deps.collect { case x: Var => (x, n) }

  def loop(deps: List[Expr], bound: List[Var], body: Expr, counters: Map[Var, Expr]): List[(Var, Option[Expr])] =
    val counters_ =
      (deps, bound) match
        case (Butlast(Counter(Ints.zero, Ints.one, n)) :: _, k :: _) => counters + (k -> n)
        case _                                                        => counters
    tag(deps) ++ deps.flatMap(dependencies(_, counters_)) ++ dependencies(body, counters_)

  // rewrite rules of -prove are simp lemmas
  def simp(attrs: Attrs): Doc =
    if attrs.contains("rw") then text("@[simp]") ~ space else empty

  // the commands of SMT-LIB that have no counterpart are comments
  def doc(cmd: Cmd): Doc =
    cmd match
      case CheckSat              => text("-- check-sat")
      case Labels                => text("-- labels")
      case GetModel              => text("-- get-model")
      case GetWitness            => text("-- get-witness")
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

      // the commands of SV-LIB have no counterpart
      case _: AnnotateTag | _: VerifyCall =>
        Error.raise("command not supported", cmd)

      // uninterpreted sorts are axiomatized types
      case DeclareSort(Con(name_, arity), _) =>
        text("axiom " + name(name_) + " :") ~~ text((List.fill(arity)("Type") :+ "Type").mkString(" → "))

      case DefineSort(Con(name_, _), params_, body, _) =>
        val params__ = if params_.isEmpty then empty else text(" (" + params_.map(param).mkString(" ") + " : Type)")
        text("abbrev " + name(name_)) ~ params__ ~~ text(":=") ~ Nest(2, hardline ~ doc(body))

      // mutually recursive datatypes in a mutual block; the selectors are not declared, Lean has no counterpart of
      // the partial functions of SMT-LIB, and the main use, the datatype Trace of teq.dfy, does not use them
      case DeclareDatatypes(cons, datas, _) =>
        val inductives = for (con, data) <- cons zip datas yield inductive(con, data)
        val opens = for con <- cons yield text("open " + name(con.name))
        val block =
          if cons.length == 1
          then inductives.head
          else text("mutual") ~ Nest(2, concat(inductives.map(hardline ~ _))) ~ hardline ~ text("end")
        join(block :: opens, hardline ~ hardline)

      case DeclareFun(Fun(name_, params_, Nil, res), _) =>
        text("axiom") ~~ text(name(name_)) ~ params(params_) ~~ text(":") ~~ doc(res)

      case DeclareFun(Fun(name_, params_, formals_, res), _) =>
        Group(text("axiom") ~~ text(name(name_)) ~ params(params_) ~~ text(":") ~ Nest(2, line ~ curried(formals_.types, res)))

      // definitions that use conditionals on propositions are not computable
      case DefineFun(fun @ Fun(name_, params_, formals_, res), body, _) =>
        if positions(fun, body).nonEmpty then folds(name_) = positions(fun, body)
        val head = text("noncomputable def") ~~ signature(name_, params_, formals_) ~~ text(":") ~~ doc(res)
        head ~~ text(":=") ~ Nest(2, hardline ~ definition(fun, body)) ~ termination(fun, body)

      // axioms and free lemmas are assumed, the other lemmas are theorems to be proved
      case Assert(Axiom, params_, phi, attrs) =>
        statement(simp(attrs) ~ text("axiom") ~~ text(named(attrs, phi)) ~ params(params_), phi, None)

      case Assert(Lemma, params_, phi, attrs) if attrs.contains("free") =>
        val (fresh, hyps) = lengths(phi)
        statement(simp(attrs) ~ text("axiom") ~~ text(named(attrs, phi)) ~ params(params_), phi, None, fresh, hyps)

      case Assert(Lemma, params_, phi, attrs) =>
        val (fresh, hyps) = lengths(phi)
        statement(simp(attrs) ~ text("theorem") ~~ text(named(attrs, phi)) ~ params(params_), phi, Some(text("by sorry")), fresh, hyps)

      // goals are anonymous
      case Assert(Goal, params_, phi, _) =>
        statement(text("example") ~ params(params_), phi, Some(text("by sorry")))

      case _: DeclareVar | _: DeclareProc | _: DefineProc | _: FuseFuns =>
        unsupported(cmd)

  // the body of a definition, whose recursion on a sequence, if |xs| == 0 then a else b for a formal parameter xs,
  // is structural in Lean as a match on the list, whose head and tail replace xs[0] and xs[1..] in b
  def definition(fun: Fun, body: Expr): Doc =
    body match
      case Ite(Eq(Seqs.len(xs: Var), Ints.zero), empty, nonempty) if fun.formals.contains(xs) =>
        val Sort(_, List(elem)) = xs.typ: @unchecked
        val used = (body.free ++ fun.formals).map(_.name.subscripted)
        val names = Iterator.iterate(("hd", "tl"))((hd, tl) => (hd + "'", tl + "'")).find((hd, tl) => !used(hd) && !used(tl)).get
        val hd = Var(Name(names._1, None), elem)
        val tl = Var(Name(names._2, None), xs.typ)
        val cases =
          List(Group(text("| [] =>") ~ Nest(2, line ~ doc(empty))),
            Group(text("| " + names._1 + " :: " + names._2 + " =>") ~ Nest(2, line ~ doc(split(xs, hd, tl, nonempty)))))
        text("match " + name(xs.name) + " with") ~ concat(cases.map(hardline ~ _))

      case _ =>
        doc(body)

  // the expression with xs[0] replaced by hd and xs[1..] by tl
  def split(xs: Var, hd: Var, tl: Var, expr: Expr): Expr =
    expr match
      case Seqs.nth(`xs`, Ints.zero)        => hd
      case Seqs.extract(`xs`, Ints.one, _)  => tl
      case _                               => expr.map(split(xs, hd, tl, _))

  // recursion on an integer, if n <= 0 then a else b for a formal parameter n, terminates by the measure n.toNat,
  // which decreases at the recursive calls in b, where n > 0
  def termination(fun: Fun, body: Expr): Doc =
    body match
      case Ite(Ints.le(n: Var, Ints.zero), _, _) if fun.formals.contains(n) && calls(fun, body) =>
        hardline ~ text("termination_by " + name(n.name) + ".toNat") ~ hardline ~ text("decreasing_by all_goals omega")

      case _ =>
        empty

  // whether `expr` calls `fun`
  def calls(fun: Fun, expr: Expr): Boolean =
    expr match
      case App(fun_, _, _, _) if fun_ == fun => true
      case _ =>
        var found = false
        expr.map { arg => found = found || calls(fun, arg); arg }
        found

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

  // the tuple types and their constructors, which are declared in the prelude of Dafny as tuple₂, tuple₃, ...
  def isTuple(name: Name, arity: Int): Boolean =
    name == Tuples.name(arity)

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
      case Trace(_, _, _, _, _) | Maps(_, _, _) | Invs(_, _, _) | History(_, _) => max - 1
      case Component(_, _)                                  => max
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

      case Seqs.nth(seq, Lit(index: BigInt, _)) if index >= 0 =>
        doc(seq, max) ~ text(".getD " + index + " default")

      case Seqs.nth(seq, index) =>
        app(doc(seq, max) ~ text(".getD"), Nil) ~~ text("(") ~ doc(index, max) ~ text(".toNat)") ~~ text("default")

      case Seqs.extract(seq, Lit(from: BigInt, _), len) if from >= 0 =>
        text("((") ~ doc(seq, max) ~ text(".drop " + from + ").take ") ~ doc(len, max) ~ text(".toNat)")

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
        doc(arg_, max) ~ text(projection(n, i))

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

        // a match on a tuple whose cases are tuples of patterns has several discriminants, match x, y with | p, q
        val tuples =
          arg_ match
            case Tuples(args) => cases.forall { case Case(Tuples(pats), _, _) => pats.length == args.length; case _ => false }
            case _           => false

        val discriminants =
          arg_ match
            case Tuples(args) if tuples => join(args.map(doc(_)), text(",") ~ space)
            case _                     => doc(arg_)

        val cases_ =
          for (Case(pat, body, _), i) <- cases.zipWithIndex
          yield
            val pat_ =
              pat match
                case Tuples(pats) if tuples => join(pats.map(pattern), text(",") ~ space)
                case _                     => pattern(pat)
            val body_ = if i < cases.length - 1 then doc(body, lowest + 1) else doc(body)
            Group(text("|") ~~ pat_ ~~ text("=>") ~ Nest(2, line ~ body_))

        Align(text("match") ~~ discriminants ~~ text("with") ~ concat(cases_.map(hardline ~ _)))

      // the combinators of trace equation systems, as applications of the functions of teq.lean by the number of
      // their dependencies (trace, trace2, ...) to the dependencies and the update as a function of the bound variables
      // the combinators of trace equation systems; several accumulators are a trace of their product, whose initial
      // value and result are tuples, and whose accumulator is bound by ⟨x₁, x₂⟩
      case Trace(inits, deps, accs, bound, results) =>
        combinator("trace", inits, deps, accs, bound, results)

      case Maps(deps, bound, update) =>
        combinator("maps", Nil, deps, Nil, bound, List(update))

      case Invs(deps, bound, body) =>
        combinator("invs", Nil, deps, Nil, bound, List(body))

      // the component i of the last value of a trace of several accumulators, selected from the nested pairs like the
      // components of tuples, and its history, the list of that component of the earlier values
      case Component(trace, i) =>
        doc(Current(trace), max) ~ text(projection(accumulators(trace), i))

      case History(trace, i) =>
        Group(text("maps") ~ Nest(2, line ~ arg(Butlast(trace)) ~ line ~ text("(fun s => s" + projection(accumulators(trace), i) + ")")))

      // the cases of an update as conditionals, where no guard holding is unspecified, as in the core (see Eps), such
      // that the completeness of the guards is an obligation of the proofs, not an assumption of the printer
      case Eps(updates) =>
        doc(updates.foldRight(Unspecified(expr.typ)) { case (Upd(cond, rhs), rest) => Ite(cond, rhs, rest) })

      case _: Old | _: Diff | _: Prop | _: Rec =>
        unsupported(expr)

  // the number of accumulators of a trace, by its type
  def accumulators(trace: Expr): Int =
    trace.typ match
      case Sort(Con.trace, List(elem)) => Trace.components(elem).length
      case _                           => Error.raise("component of an expression that is not a trace", trace)

  // the selection of the component i of n nested pairs, (a, (b, c)): .1 for a, .2.1 for b, .2.2 for c
  def projection(n: Int, i: Int): String =
    (List.fill(i)(".2") ++ (if i < n - 1 then List(".1") else Nil)).mkString

  // a combinator over its dependencies, which are zipped if there are several, List.zip d₁ (List.zip d₂ d₃), whose
  // update is a function of the values of the dependencies as a tuple, fun ⟨b₁, b₂, b₃⟩ => ..., after the accumulators
  // of a trace, also a tuple if there are several, whose initial values and results are then tuples
  def combinator(name_ : String, inits: List[Expr], deps: List[Expr], accs: List[Var], bound: List[Var], results: List[Expr]): Doc =
    def tuple(xs: List[Var]) =
      if xs.length == 1 then name(xs.head.name) else xs.map(x => name(x.name)).mkString("⟨", ", ", "⟩")
    def product(es: List[Expr]) =
      if es.length == 1 then doc(es.head) else text("(") ~ Align(join(es.map(doc(_)), text(",") ~ line)) ~ text(")")

    val init = inits match
      case Nil       => Nil
      case List(one) => List(arg(one))
      case _         => List(product(inits))
    val zipped = deps.init.foldRight(arg(deps.last))((dep, rest) => text("(List.zip") ~~ arg(dep) ~~ rest ~ text(")"))
    val params_ = ((if accs.isEmpty then Nil else List(tuple(accs))) :+ tuple(bound)).mkString(" ")
    val fun = Group(text("fun " + params_ + " =>") ~ Nest(2, line ~ product(results)))
    Group(text(name_) ~ Nest(2, concat(init.map(line ~ _)) ~ line ~ zipped ~ line ~ text("(") ~ Align(fun) ~ text(")")))

  // patterns of constructors, whose wildcards are named apart by indices (see dafny.Parser), which are not printed
  def pattern(pat: Expr): Doc =
    pat match
      case Var(Name("_", Some(_)), _) =>
        text("_")

      case App(fun, _, _, Nil) =>
        text("." + name(fun.name))

      // tuples of patterns are pairs, which nest like the tuples (see the selectors tupleₙ_i)
      case Tuples(args) if args.length > 1 =>
        text("(") ~ join(args.map(pattern), text(",") ~ space) ~ text(")")

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
