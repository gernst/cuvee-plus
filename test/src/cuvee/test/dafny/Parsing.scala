package cuvee.test
package dafny

import utest._

import cuvee.dafny.Source

object Parsing extends TestSuite:
  // Dafny examples must parse without errors
  val tests =
    Examples.tests(Examples.find(os.sub / "dafny", "dfy")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

// derivatives are with respect to variables on real only
object Derivatives extends TestSuite:
  def errors(text: String) =
    val file = os.temp(text, suffix = ".dfy")
    Examples.errors("-print", "null", file.toString)

  val tests = Tests:
    test("real"):
      errors("method m(x: real) returns (y: real) { y := (x :: x * x)'; }") ==> Nil

    test("int"):
      errors("method m(n: int) returns (k: int) { k := (n :: n * n)'; }") ==>
        List("derivative with respect to variables that are not real")

// differential equations are for variables on real only
object Odes extends TestSuite:
  def errors(text: String) =
    val file = os.temp(text, suffix = ".dfy")
    Examples.errors("-print", "null", file.toString)

  val tests = Tests:
    test("real"):
      errors("method m(g: real) returns (x: real) { x' == g; }") ==> Nil

    test("int"):
      errors("method m(g: int) returns (x: int) { x' == g; }") ==>
        List("differential equations for variables that are not real")

// slices and updates are on sequences only, indexing falls back to arrays
object Sequences extends TestSuite:
  def errors(text: String) =
    val file = os.temp(text, suffix = ".dfy")
    Examples.errors("-print", "null", file.toString)

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

    test("indexing of int"):
      errors("function f(n: int): int { n[0] }") ==> List("operator not defined for type")

    test("concatenation of int and seq"):
      errors("function f(s: seq<int>): seq<int> { s + 1 }") ==> List("type mismatch")

// global variables are modified by methods with a modifies clause only
object Globals extends TestSuite:
  def errors(text: String) =
    val file = os.temp(text, suffix = ".dfy")
    Examples.errors("-print", "null", file.toString)

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

// parallel composition of calls that do not share modified variables other than the history
object Parallel extends TestSuite:
  def errors(text: String) =
    val file = os.temp(text, suffix = ".dfy")
    Examples.errors("-print", "null", file.toString)

  val history = "var history: seq<event<int>>; "
  val p = "method p(n: int) returns (x: int) modifies history assumes true commits true { x := n; } "

  val tests = Tests:
    test("parallel"):
      errors(history + p + "method m() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(2); } }") ==> Nil

    test("shared"):
      errors(history + p + "method m() returns (x: int) modifies history { parallel { x := p(1); x := p(2); } }") ==>
        List("parallel calls share modified variables")

    test("read"):
      errors(history + p + "method m() returns (x: int, y: int) modifies history { parallel { x := p(1); y := p(x); } }") ==>
        List("parallel calls share modified variables")

// testers x.C? on variables and type annotations e as T
object Datatypes extends TestSuite:
  def errors(text: String) =
    val file = os.temp(text, suffix = ".dfy")
    Examples.errors("-print", "null", file.toString)

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

// check-sat is the command check, without semicolon, which is printed back the same way
object Check extends TestSuite:
  val tests = Tests:
    test("roundtrip"):
      val (_, cmds) = Source(new java.io.StringReader("const c: int\ncheck\naxiom c == 0"))
      val cmds_ = cmds.toList
      assert(cmds_.contains(cuvee.core.CheckSat))
      cuvee.dafny.Printer.lines(cuvee.core.CheckSat) ==> List("check", "")

// preconditions are evaluated at the entry of a method, where old values are the current ones
object OldInPrecondition extends TestSuite:
  def errors(text: String) =
    val file = os.temp(text, suffix = ".dfy")
    Examples.errors("-print", "null", file.toString)

  val tests = Tests:
    test("ensures"):
      errors("var g: int; method m() modifies g ensures g == old(g) + 1 { g := g + 1; }") ==> Nil

    test("requires"):
      errors("var g: int; method m() modifies g requires old(g) == 0 { g := g + 1; }") ==>
        List("precondition refers to old values")

// goals are parsed like lemmas, e.g. the output of -verify
object Goals extends TestSuite:
  val tests = Tests:
    test("goal"):
      val (_, cmds) = Source(new java.io.StringReader("goal {:rw} forall x: int :: x < x + 1"))
      val cuvee.core.Assert(justify, _, _, attrs) = cmds.last: @unchecked
      justify ==> cuvee.core.Goal
      assert(attrs.contains("rw"))
