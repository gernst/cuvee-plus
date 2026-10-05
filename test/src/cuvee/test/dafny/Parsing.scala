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
        List("parallel calls share modified variables")

    // the history ticks after a differential equation
    test("tick"):
      errors(history + "method m(g: real) returns (x: real) modifies history { ode t :: x' == g; }") ==> Nil
      errors(history + "method m(g: real) returns (x: real) { ode t :: x' == g; }") ==>
        List("differential equation ticks the history, which is not in the modifies clause")

    test("read"):
      errors(history + p + "method m() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(x); } }") ==>
        List("parallel calls share modified variables")

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

    test("old in precondition"):
      errors("var g: int; method m() modifies g requires old(g) == 0 { g := g + 1; }") ==>
        List("precondition refers to old values")

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

    test("annotation"):
      errors(list + "function f(xs: list<int>): bool { xs != nil as list<int> }") ==> Nil

    test("wrong annotation"):
      errors(list + "function f(): bool { 0 as bool }") ==> List("type mismatch")

// in axioms, lemmas, and goals, if φ then ψ without else is φ ==> ψ with the lowest precedence,
// also below the quantifiers at the top, inside of expressions, if-then-else must have an else branch
object Conditionals extends TestSuite:
  import cuvee.core.{Imp, Ite, All}

  def formula(text: String) =
    val (_, cmds) = Source(new java.io.StringReader("predicate p(x: int)\npredicate q(x: int)\n" + text))
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

    test("expressions need else"):
      errors("axiom (if 1 < 2 then true) == true") ==> List("parse error")

// chained comparisons x < y <= z are the conjunctions x < y && y <= z, which must not mix directions,
// parenthesized comparisons do not chain
object Chains extends TestSuite:
  import cuvee.core.{And, Eq, Le, Lt, Var, Sort}

  def formula(text: String) =
    val (_, cmds) = Source(new java.io.StringReader("lemma forall i: int, j: int, n: int, b: bool :: " + text))
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
    Source(new java.io.StringReader(text))._2.toList

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
      val file = Examples.root / "dafny" / "mutual.dfy"
      val (cmds, errors) = Examples.output("-print", "null", file.toString)
      errors ==> Nil
      val groups =
        cmds.collect { case cuvee.core.DeclareDatatypes(cons, _, _) => cons.map(_.name.name) }
          .filterNot(_.exists(_.startsWith("tuple")))
      groups ==> List(List("Tree", "Forest"), List("Box"))
