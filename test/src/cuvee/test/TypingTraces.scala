package cuvee.test

import utest._

import cuvee.core._

// type checking of the combinators trace, map, and all
object TypingTraces extends TestSuite:
  val state = cuvee.smtlib.Source(new java.io.StringReader(""))._1

  val n = Var("n", Sort.int)
  val s = Var("s", Sort.int)
  val j = Var("j", Sort.int)
  val p = Var("p", Sort.bool)
  val J = Var("J", Sort.seq(Sort.int))
  val B = Var("B", Sort.seq(Sort.bool))

  def check(expr: Expr, typ: Type) =
    Type.check(state, Scope.empty, expr, typ)

  def error(expr: Expr, typ: Type): String =
    try
      check(expr, typ)
      "no error"
    catch case cuvee.Error(msg, _*) => msg

  val tests = Tests:
    test("trace"):
      val trace = Trace(Zero.int, List(J), s, List(j), List(Upd(True, Plus.int(s, j))))
      check(trace, Sort.trace(Sort.int)) ==> trace
      error(trace, Sort.seq(Sort.int)) ==> "type mismatch"

    // the type of the bound variables is inferred from the dependencies
    test("inference"):
      val a = Param("a").fresh
      val x = Var("x", a)
      // as built by the parsers, with the expected types of the arguments
      val not = App(Fun.not, List(Sort.bool), Sort.bool, List(x))
      val trace = Maps(List(B), List(x), List(Upd(x, One.int), Upd(not, Zero.int)))
      val Maps(_, List(x_), _) = check(trace, Sort.seq(Sort.int)): @unchecked
      x_.typ ==> Sort.bool

    test("dependencies"):
      val trace = Trace(Zero.int, List(B), s, List(j), List(Upd(True, s)))
      error(trace, Sort.trace(Sort.int)) ==> "type mismatch"
      error(Trace(Zero.int, Nil, s, Nil, List(Upd(True, s))), Sort.trace(Sort.int)) ==> "combinator without dependencies"

    test("guards"):
      val trace = Trace(Zero.int, List(J), s, List(j), List(Upd(j, s)))
      error(trace, Sort.trace(Sort.int)) ==> "type mismatch"

    test("map"):
      val map = Maps(List(J), List(j), List(Upd(Lt.int(j, n), j), Upd(Not(Lt.int(j, n)), n)))
      check(map, Sort.seq(Sort.int)) ==> map
      error(Maps(List(J), List(j), List(Upd(Lt.int(j, n), j), Upd(Not(Lt.int(j, n)), True))), Sort.seq(Sort.int)) ==> "type mismatch"

    test("all"):
      val all = Invs(List(J, B), List(j, p), Or(p, Lt.int(j, n)))
      check(all, Sort.bool) ==> all
      error(Invs(List(J), List(j), j), Sort.bool) ==> "type mismatch"
