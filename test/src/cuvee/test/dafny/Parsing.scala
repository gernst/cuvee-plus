package cuvee.test
package dafny

import utest._

object Parsing extends TestSuite:
  // Dafny examples must parse without errors
  val tests =
    Examples.tests(Examples.find(os.sub, "dfy")): file =>
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
      errors("function f(a: array<int,int>): bool { a[1..] == a }") ==>
        List("slice of an expression that is not a sequence")

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
