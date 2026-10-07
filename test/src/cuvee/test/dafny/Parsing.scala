package cuvee.test
package dafny

import utest._

import cuvee.dafny.Source

object Parsing extends TestSuite:
  // Dafny examples must parse without errors, with the options they state
  val tests =
    Examples.tests(Examples.find(os.sub / "dafny", "dfy") ++ Examples.find(os.sub / "hybrid", "dfy")): file =>
      Examples.errors(List("-print", "null") ++ Examples.options(file) :+ file.toString*) ==> Nil

// derivatives and differential equations are for variables on real only,
// parallel composition of calls that do not share modified variables other than the history,
// with -hybrid, which declares the history
object Hybrid extends TestSuite:
  def errors(text: String) =
    Examples.check("dfy", text, "-hybrid")

  // the input declares the global history, whose type is declared by -hybrid
  val history = "var history: history<int> "
  val p = "method p(n: int) returns (x: int) modifies history assumes true commits true { x := n; } "

  val tests = Tests:
    test("derivatives"):
      errors("method m(x: real) returns (y: real) { y := (x :: x * x)'; }") ==> Nil
      errors("method m(n: int) returns (k: int) { k := (n :: n * n)'; }") ==>
        List("derivative with respect to variables that are not real")

    test("differential equations"):
      errors("method m(g: real) returns (x: real) { ode t :: x' == g + t; }") ==> Nil
      errors("method m(g: int) returns (x: int) { ode t :: x' == g; }") ==>
        List("differential equations for variables that are not real")
      errors("method m(g: int) returns (x: real) { ode t :: x' == t + g; }") ==> List("type mismatch")

    test("parallel"):
      errors(history + p + "method m() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(2); } }") ==> Nil

    test("shared"):
      errors(history + p + "method m() returns (x: int) modifies history { parallel { x := p(1); x := p(2); } }") ==>
        List("parallel programs share modified variables")

    // the history ticks after a differential equation
    test("tick"):
      errors(history + "method m(g: real) returns (x: real) modifies history { ode t :: x' == g; }") ==> Nil
      errors(history + "method m(g: real) returns (x: real) { ode t :: x' == g; }") ==>
        List("differential equation ticks the history, which is not in the modifies clause")

    test("read"):
      errors(history + p + "method m() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(x); } }") ==>
        List("parallel programs share modified variables")

    // parallel composition of other statements is parsed, but not verified
    test("not calls"):
      val text = "method m() returns (x: int, y: int) { parallel { x := 1; y := 2; } }"
      errors(text) ==> Nil
      Examples.check("dfy", text, "-hybrid", "-verify") ==> List("parallel composition of statements that are not calls")

// assignments to elements a[i][j] := v are updates a := a[i := a[i][j := v]] of arrays, sequences, and maps
object Assignments extends TestSuite:
  def errors(text: String) =
    Examples.check("dfy", text)

  // the output printed in Dafny, without errors
  def printed(text: String): String =
    val file = os.temp(text, suffix = ".dfy")
    val out = os.temp(suffix = ".dfy")
    Examples.errors(file.toString, "-o", out.toString) ==> Nil
    os.read(out)

  val array = "method m(a: array<int, int>) returns (b: array<int, int>) { b := a; "

  val tests = Tests:
    test("array"):
      printed(array + "b[0] := 1; }") ==> printed(array + "b := b[0 := 1]; }")

    test("nested"):
      val nested = "method m(a: array<int, array<int, int>>) returns (b: array<int, array<int, int>>) { b := a; "
      printed(nested + "b[0][1] := 2; }") ==> printed(nested + "b := b[0 := b[0][1 := 2]]; }")

    test("sequences and maps"):
      errors("method m(s: seq<int>) returns (t: seq<int>) { t := s; t[0] := 1; }") ==> Nil
      errors("method m(n: map<int, bool>) returns (o: map<int, bool>) { o := n; o[0] := true; }") ==> Nil

    // elements of the same variable cannot be assigned at once, since the variable would be assigned twice
    test("parallel"):
      val two = "method m(a: array<int, int>) returns (b: array<int, int>, c: int) { b := a; "
      printed(two + "b[0], c := 1, 2; }") ==> printed(two + "b, c := b[0 := 1], 2; }")
      errors(array + "b[0], b[1] := b[1], b[0]; }") ==> List("duplicate variables")

    test("results of calls"):
      errors("method p() returns (x: int) " + array + "b[0] := p(); }") ==> List("results of calls must be assigned to variables")

// function types of 1 to 10 arguments, declared in the prelude, and lambdas, whose variables are annotated
object Functions extends TestSuite:
  def errors(text: String) =
    Examples.check("dfy", text)

  val tests = Tests:
    test("lambdas"):
      errors("function f(): (int, bool) -> int { (x: int, b: bool) => if b then x else 0 }") ==> Nil
      errors("function f(): int -> bool -> int { (x: int) => (b: bool) => x }") ==> Nil
      errors("function f(): int -> int { (x: bool) => 0 }") ==> List("type mismatch")
      errors("function f(): int -> int { (x: int, y: int) => x }") ==> List("type mismatch")

    test("arguments"):
      val ten = List.fill(10)("int").mkString("(", ", ", ")")
      errors("function f(g: " + ten + " -> int): bool { true }") ==> Nil
      errors("function f(g: " + List.fill(11)("int").mkString("(", ", ", ")") + " -> int): bool { true }") ==> List("sort not declared")

    // variables of function type before functions of the same name, then constants of function type, then members
    test("applications"):
      errors("function f(g: (int, bool) -> int): int { g(1, true) }") ==> Nil
      errors("function c(): int -> int function f(): int { c(1) }") ==> Nil
      errors("function g(x: int): bool function f(g: int -> int): int { g(1) }") ==> Nil
      errors("function f(x: int): int { x(1) }") ==> List("application of a value that is not a function")
      errors("function f(g: int -> int): int { g(1, 2) }") ==> List("type mismatch")
      errors("function f(g: int -> int): bool { g(1) }") ==> List("type mismatch")

    // the variables of lambdas must be annotated with their types
    test("annotations"):
      errors("function f(): int -> int { x => x }") ==> List("parse error")

    test("boogie"):
      val file = os.temp("function f(): int -> int { (x: int) => x }", suffix = ".dfy")
      Examples.errors("-print", "bpl", file.toString) ==> List("lambda of function type not supported in Boogie")

    // applications and lambdas are printed as in higher-order SMT-LIB, and the declarations of the function types
    // and the application functions ({:ho}) are not passed to solvers
    test("smtlib"):
      val file = os.temp("function f(g: (int, int) -> int): int { g(1, 2) } function h(): (int, int) -> int { (x: int, y: int) => x }", suffix = ".dfy")
      val out = os.temp(suffix = ".smt2")
      Examples.errors("-print", "smt2", "-o", out.toString, file.toString) ==> Nil
      val text = os.read(out).replaceAll("\\s+", " ")
      assert(text.contains("(@ g 1 2)") && text.contains("(-> Int Int Int)") && text.contains("(lambda ((x Int) (y Int)) x)"))
      assert(!text.contains("arrow") && !text.contains("apply"))
      Examples.check("dfy", "var g: int; method m() modifies g ensures g == 1 { g := 1; }", "-verify", "-z3") ==> Nil

// slices and updates are on sequences only, indexing falls back to arrays
object Sequences extends TestSuite:
  def errors(text: String) =
    Examples.check("dfy", text)

  val tests = Tests:
    test("seq"):
      errors("function f(s: seq<int>): bool { s[1..] + s[..1] == [s[0]] + s[1..|s|] }") ==> Nil

    test("slice of array"):
      errors("function f(a: array<int,int>): bool { a[1..] == a }") ==> List("type mismatch")

    // indexing is resolved by overloading once the type of the base is known
    test("indexing"):
      errors("function id<a>(x: a): a { x } function f(s: seq<int>): bool { id(s)[0] == s[1] }") ==> Nil
      errors("function f(s: seq<bool>, i: int, j: int): bool { s[i] == s[j] && s[i := s[j]] == s }") ==> Nil
      errors("function f(a: array<int,bool>, i: int): bool { a[i] && a[i := false] == a }") ==> Nil
      errors("type S = seq<int> function f(s: S): int { s[0] + |s| }") ==> Nil

    // the type of a polymorphic constant is determined by an overloaded operator to its right,
    // and remains ambiguous without one
    test("polymorphic constants"):
      errors("function c<a>(): a function f(s: seq<int>): bool { c() + c() == s[0] }") ==> Nil
      errors("function c<a>(): a function f(): bool { c() + c() == c() }") ==> List("ambiguous overloaded operator")

    test("indexing of int"):
      errors("function f(n: int): int { n[0] }") ==> List("operator not defined for type")

    test("concatenation of int and seq"):
      errors("function f(s: seq<int>): seq<int> { s + 1 }") ==> List("type mismatch")

// global variables are modified by methods with a modifies clause only,
// preconditions are evaluated at the entry of a method, where old values are the current ones
object Globals extends TestSuite:
  def errors(text: String) =
    Examples.check("dfy", text)

  val tests = Tests:
    test("modifies"):
      errors("var g: int; method m() modifies g ensures g == old(g) + 1 { g := g + 1; }") ==> Nil

    test("not modified"):
      errors("var g: int; method m() { g := 1; }") ==> List("assignment to variables that must not be modified")

    test("local in modifies clause"):
      errors("method m(x: int) modifies x { }") ==>
        List("modifies clause of method lists variables that are not global")

    test("call"):
      errors("var g: int; method m() modifies g { } method n() { m(); }") ==>
        List("call modifies variables that are not in the modifies clause")

    // loops modify the global variables in their modifies clause only, directly or by calls,
    // which must be modifiable by the enclosing method
    test("loops"):
      val p = "var g: int; method p() modifies g { } "
      errors(p + "method m() modifies g { while true modifies g { g := 1; p(); } }") ==> Nil
      errors(p + "method m() modifies g { while true { g := 1; } }") ==>
        List("assignment to variables that must not be modified")
      errors(p + "method m() modifies g { while true { p(); } }") ==>
        List("call modifies variables that are not in the modifies clause")
      errors(p + "method m() { while true modifies g { } }") ==>
        List("modifies clause of loop lists global variables that are not modifiable")

    // the precondition is evaluated at the entry, where old(e) is e
    test("old in precondition"):
      Examples.check("dfy", "var g: int; method m() modifies g requires old(g) == 0 ensures g == 1 { g := g + 1; }", "-verify", "-z3") ==> Nil

// testers x.C? on variables and type annotations e as T
object Datatypes extends TestSuite:
  def errors(text: String) =
    Examples.check("dfy", text)

  val list = "datatype list<a> = nil | cons(head: a, tail: list<a>) "

  val tests = Tests:
    test("tester"):
      errors(list + "function f(xs: list<int>): bool { xs.cons? && !xs.nil? }") ==> Nil

    test("tester on a call"):
      errors(list + "function g(): list<int> function f(): bool { g().nil? }") ==>
        List("tester on an expression that is not a variable")

    test("unknown tester"):
      errors(list + "function f(xs: list<int>): bool { xs.none? }") ==> List("constructor not declared")

    // m.Keys and m.Values on other types than maps are rejected by type checking
    test("keys"):
      errors("function f(m: map<int, bool>): set<int> { m.Keys }") ==> Nil
      errors("function f(s: set<int>): set<int> { s.Keys }") ==> List("type mismatch")

    // inside the members of a type, its fields, functions, and methods are accessible without this
    test("implicit this"):
      val pair = "datatype pair = pair(fst: int, snd: int) { "
      errors(pair + "function sum(): int { fst + snd } function twice(): int { sum() + this.sum() } }") ==> Nil
      errors(pair + "method get() returns (x: int) { x := fst; } method get2() returns (y: int) { y := get(); } }") ==> Nil
      errors("function f(): int { g(1) }") ==> List("unresolved identifier")

    test("annotation"):
      errors(list + "function f(xs: list<int>): bool { xs != nil as list<int> }") ==> Nil

    test("wrong annotation"):
      errors(list + "function f(): bool { 0 as bool }") ==> List("type mismatch")

// if φ then ψ without else is φ ==> ψ, also inside of expressions, and else belongs to the innermost if
object Conditionals extends TestSuite:
  import cuvee.core.{Imp, Ite, All}

  def formula(text: String) =
    val (_, cmds) = Examples.source(Source, new java.io.StringReader("predicate p(x: int)\npredicate q(x: int)\n" + text))
    val cuvee.core.Assert(_, _, phi, _) = cmds.last: @unchecked
    phi

  def errors(text: String) =
    Examples.check("dfy", text)

  val tests = Tests:
    test("implication"):
      val Imp(_, cuvee.core.And(_)) = formula("axiom if p(0) then q(0) && q(1)"): @unchecked

    test("below quantifiers"):
      val All(_, Imp(_, _)) = formula("lemma forall x: int :: if p(x) then q(x)"): @unchecked

    // the else belongs to the inner if, which must have one
    test("nested"):
      val Imp(_, Ite(_, _, _)) = formula("goal if p(0) then if q(0) then p(1) else q(1)"): @unchecked

    test("else"):
      val Ite(_, _, _) = formula("axiom if p(0) then q(0) else q(1)"): @unchecked

    test("inside expressions"):
      val cuvee.core.Eq(Imp(_, _), _) = formula("axiom (if p(0) then q(0)) == q(1)"): @unchecked

    // the cases of updates begin with case, if-then-else expressions need no parentheses there
    test("updates are cases"):
      val update = "type Trace<a>\nfunction f(J: seq<int>): bool { trace(0, for J do s, j :: %s) == trace(0, for J do s, j :: s) }"
      errors(update.format("if j < 0 then s else s + 1")) ==> Nil
      errors(update.format("case j < 0 => s case 0 <= j => s + 1")) ==> Nil
      errors(update.format("if j < 0 then s, if 0 <= j then s + 1")) ==> List("parse error")

// chained comparisons x < y <= z are the conjunctions x < y && y <= z, which must not mix directions,
// parenthesized comparisons do not chain
object Chains extends TestSuite:
  import cuvee.core.{And, Eq, Le, Lt, Var, Sort}

  def formula(text: String) =
    val (_, cmds) = Examples.source(Source, new java.io.StringReader("lemma forall i: int, j: int, n: int, b: bool :: " + text))
    val cuvee.core.Assert(_, _, cuvee.core.All(_, phi), _) = cmds.last: @unchecked
    phi

  def errors(text: String) =
    Examples.check("dfy", "function f(i: int, j: int, n: int): bool { " + text + " }")

  val i = Var("i", Sort.int)
  val j = Var("j", Sort.int)
  val n = Var("n", Sort.int)
  val b = Var("b", Sort.bool)

  val tests = Tests:
    test("chains"):
      formula("0 <= i < n") ==> And(Le.int(cuvee.core.Zero.int, i), Lt.int(i, n))
      formula("i == j == n") ==> And(Eq(i, j), Eq(j, n))
      formula("i <= j == n < 1") ==> And(And(Le.int(i, j), Eq(j, n)), Lt.int(n, cuvee.core.One.int))

    test("parentheses"):
      formula("(i == j) == b") ==> Eq(Eq(i, j), b)

    test("directions"):
      errors("i < j > n") ==> List("chained comparisons in different directions")
      errors("n > j >= i == 0") ==> Nil

// the commands and declarations of the dialect: check-sat is check, goals are parsed like lemmas (e.g. the output
// of -verify), the type string is String in the core, top-level commands are printed without semicolon,
// and the semicolon after global variables is optional
object Commands extends TestSuite:
  def parse(text: String) =
    Examples.source(Source, new java.io.StringReader(text))._2.toList

  val tests = Tests:
    test("check"):
      assert(parse("const c: int\ncheck\naxiom c == 0").contains(cuvee.core.CheckSat))
      cuvee.dafny.Printer.lines(cuvee.core.CheckSat) ==> List("check", "")

    test("goal"):
      val cuvee.core.Assert(justify, _, _, attrs) = parse("goal {:rw} forall x: int :: x < x + 1").last: @unchecked
      justify ==> cuvee.core.Goal
      assert(attrs.contains("rw"))

    test("string"):
      val decls = parse("const s: string := \"a\"").collect { case cmd @ cuvee.core.DefineFun(fun, _, _) if fun.name.name == "s" => cmd }
      decls.map(_.fun.res) ==> List(cuvee.core.Sort.string)
      decls.flatMap(cuvee.dafny.Printer.lines).head.trim ==> "const s: string := \"a\""

    test("global variables"):
      for text <- List("var g: int\nconst c: int", "var g: int;\nconst c: int")
      do
        val decls = parse(text).collect { case cmd @ cuvee.core.DeclareVar(x, _) if x.name.name == "g" => cmd }
        decls.flatMap(cuvee.dafny.Printer.lines).head.trim ==> "var g: int"

    test("semicolons"):
      cuvee.dafny.Printer.lines(cuvee.core.Push(1)).head ==> "push 1"
      cuvee.dafny.Printer.lines(cuvee.core.GetModel).head ==> "model"

// consecutive datatypes are declared by groups of mutually recursive ones, each after those that it refers to
object MutualDatatypes extends TestSuite:
  val tests = Tests:
    test("groups"):
      val file = Examples.root / "dafny" / "language" / "mutual.dfy"
      val (cmds, errors) = Examples.output("-print", "null", file.toString)
      errors ==> Nil
      val groups =
        cmds.collect { case cuvee.core.DeclareDatatypes(cons, _, _) => cons.map(_.name.name) }
          .filterNot(_.exists(_.startsWith("tuple")))
      groups ==> List(List("Tree", "Forest"), List("Box"))

// bitvectors bv8, ...: the operators are resolved by overloading on the width, numeric literals take the type of
// their context, integers by default, and are reduced modulo 2^n; e as int and e as bv8 convert
object Bitvectors extends TestSuite:
  import cuvee.core._

  def errors(text: String) =
    Examples.check("dfy", text)

  // the expressions of the goals of a program
  def goal(text: String): Expr =
    val file = os.temp(text, suffix = ".dfy")
    val (cmds, errors) = Examples.output("-print", "null", file.toString)
    errors ==> Nil
    cmds.collectFirst { case Assert(_, _, phi, _) => phi }.get

  val x = Var("x", BitVec(8))

  val tests = Tests:
    test("literals"):
      goal("lemma 1 + 2 == 3") ==> Eq(Plus.int(Lit(BigInt(1), Sort.int), Lit(BigInt(2), Sort.int)), Lit(BigInt(3), Sort.int))
      goal("lemma forall x: bv8 :: x != 300") ==> All(List(x), Not(Eq(x, BitVecs.lit(44, 8))))
      errors("function f(s: seq<int>): bool { s == 1 }") ==> List("type mismatch")

    test("operators"):
      val add = BitVecs.fun("bvadd", Nil, List(8, 8)).get
      val ult = BitVecs.fun("bvult", Nil, List(8, 8)).get
      goal("lemma forall x: bv8 :: x < x + 1") ==> All(List(x), App(ult, List(x, App(add, List(x, BitVecs.lit(1, 8))))))
      errors("function f(x: bv8, y: bv16): bv8 { x + y }") ==> List("type mismatch")
      errors("function f(x: bv8): bool { !x }") ==> List("type mismatch")

    test("conversions"):
      val bv2nat = BitVecs.fun("bv2nat", Nil, List(8)).get
      goal("lemma forall x: bv8 :: (x as int) < 256") ==> All(List(x), Lt.int(App(bv2nat, List(x)), Lit(BigInt(256), Sort.int)))
      goal("lemma forall n: int :: ((n as bv8) as int) < 256") ==>
        All(List(Var("n", Sort.int)), Lt.int(App(bv2nat, List(App(BitVecs.int2bv(8), List(Var("n", Sort.int))))), Lit(BigInt(256), Sort.int)))
      errors("function f(x: bool): int { x as int }") ==> List("operator not defined for type")
