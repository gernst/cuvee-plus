package cuvee.test

import utest._

import _root_.util.Name
import cuvee.core._

// match expressions: the variables of the patterns are bound in the bodies and conditions
object Matching extends TestSuite:
  val list = Sort(Con("List", 0), Nil)
  val nil = Fun("nil", Nil, Nil, list)
  val cons = Fun("cons", Nil, Fun.formals(Sort.int, list), list)
  val head = Fun("head", Nil, Fun.formals(list), Sort.int)
  val tail = Fun("tail", Nil, Fun.formals(list), list)
  val data = Datatype(Nil, List(nil -> Nil, cons -> List(head, tail)))

  // the datatype (declare-datatype List ((nil) (cons (head Int) (tail List))))
  val state =
    val init = Examples.source(cuvee.smtlib.Source, new java.io.StringReader(""))._1
    init.declare(Name("List", None), 0, Attrs.empty).declare(data).define(Name("List", None), data)

  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val n = Var("n", Sort.int)
  val xs = Var("xs", list)
  val ys = Var("ys", list)

  def app(fun: Fun, args: Expr*) =
    App(fun, args.toList)

  // match ys with nil => n | cons(x, xs) => x + y, under the condition x < n in the second case
  val expr =
    Match(ys, List(Case(app(nil), n, True), Case(app(cons, x, xs), Ints.plus(x, y), Ints.lt(x, n))))

  def check(expr: Expr, typ: Type) =
    Type.check(state, Scope.empty, expr, typ)

  def error(expr: Expr, typ: Type): String =
    try
      check(expr, typ)
      "no error"
    catch case cuvee.Error(msg, _*) => msg

  val tests = Tests:
    test("free"):
      expr.free ==> Set(ys, n, y)
      expr.typ ==> Sort.int

      // the patterns are not visited
      val visited = List.newBuilder[Expr]
      expr.map: arg =>
        visited += arg
        arg
      visited.result() ==> List(ys, n, True, Ints.plus(x, y), Ints.lt(x, n))

    // the variables of the patterns are not substituted, and renamed if they would capture
    test("substitution"):
      Subst.from(List(x, n), List(y, y))(expr) ==>
        Match(ys, List(Case(app(nil), y, True), Case(app(cons, x, xs), Ints.plus(x, y), Ints.lt(x, y))))

      val Match(_, List(_, Case(App(_, _, _, List(x_ : Var, `xs`)), body, cond))) = Subst.from(List(y), List(x))(expr): @unchecked
      assert(x_ != x)
      body ==> Ints.plus(x_, x)
      cond ==> Ints.lt(x_, n)

    test("map"):
      expr.map(e => Subst.from(List(x), List(n))(e)) ==>
        Match(ys, List(Case(app(nil), n, True), Case(app(cons, x, xs), Ints.plus(n, y), Ints.lt(n, n))))

    test("typing"):
      check(expr, Sort.int) ==> expr
      error(expr, Sort.bool) ==> "type mismatch"
      error(Match(x, expr.cases), Sort.int) ==> "type mismatch"
      error(Match(ys, Nil), Sort.int) ==> "match without cases"

    // patterns are linear and built from constructors and variables
    test("patterns"):
      error(Match(ys, List(Case(app(cons, x, app(cons, x, xs)), x, True))), Sort.int) ==> "invalid pattern"
      error(Match(ys, List(Case(app(cons, Ints.plus(x, y), xs), x, True))), Sort.int) ==> "invalid pattern"
      check(Match(ys, List(Case(app(cons, x, app(cons, y, xs)), x, True), Case(ys, n, True))), Sort.int)

    test("printing"):
      val unguarded = Match(ys, List(Case(app(nil), n, True), Case(app(cons, x, xs), x, True)))
      cuvee.smtlib.Printer.lines(unguarded).map(_.trim).mkString(" ") ==> "(match ys ((nil n) ((cons x xs) x)))"
