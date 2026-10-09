package cuvee.test

import utest._

import cuvee.Config
import cuvee.Error
import cuvee.core._
import cuvee.simplify.Context
import cuvee.simplify.Simplify

// recursive functions (Rec), which have no syntax: a function bound in its cases, whose patterns apply it
// to patterns of its arguments, with guards as conditions
object Recs extends TestSuite:
  val n = Var("n", Sort.int)
  val m = Var("m", Sort.int)
  val c = Var("c", Sort.int)
  val sum = Fun("sum", Nil, List(Var("x", Sort.int)), Sort.int)
  val int = Arrow(List(Sort.int), Sort.int)

  // sum(n) = 0 if n <= 0, n + sum(n - 1) if 0 < n
  val sums =
    Rec(
      sum,
      List(
        Case(App(sum, List(n)), Ints.zero, Ints.le(n, Ints.zero)),
        Case(App(sum, List(n)), Ints.plus(n, App(sum, List(Ints.minus(n, Ints.one)))), Ints.lt(Ints.zero, n))
      )
    )

  // the message of the error of type checking, if any
  def error(expr: Expr, typ: Type): String =
    try
      Type.check(State.empty, Scope.empty, expr, typ)
      ""
    catch case Error(msg, _*) => msg

  val tests = Tests:
    // a function value whose pattern variables are bound, and the function is no variable
    test("free"):
      sums.typ ==> int
      sums.free ==> Set()
      Rec(sum, List(Case(App(sum, List(n)), Ints.plus(n, c), True))).free ==> Set(c)

    // the patterns apply the function to distinct variables, the bodies have the type of its result
    test("check"):
      Type.check(State.empty, Scope.empty, sums, int) ==> sums
      error(sums, Arrow(List(Sort.int), Sort.bool)) ==> "type mismatch"
      error(Rec(sum, Nil), int) ==> "recursive function without cases"
      error(Rec(sum, List(Case(n, n, True))), int) ==> "pattern does not apply the recursive function"
      error(Rec(sum, List(Case(App(sum, List(n)), True, True))), int) ==> "type mismatch"
      val add = Fun("add", Nil, List(Var("x", Sort.int), Var("y", Sort.int)), Sort.int)
      val adds = Arrow(List(Sort.int, Sort.int), Sort.int)
      error(Rec(add, List(Case(App(add, List(n, n)), n, True))), adds) ==> "invalid pattern"
      val pair = Rec(add, List(Case(App(add, List(n, m)), Ints.plus(n, m), True)))
      Type.check(State.empty, Scope.empty, pair, adds) ==> pair

    // the pattern variable n would capture the replacement of c, it is renamed in the pattern and the body,
    // by substitution and by the elimination of old, which replaces c inside of old(c)
    test("capture"):
      val rec = Rec(sum, List(Case(App(sum, List(n)), Ints.plus(n, c), True)))
      val Rec(_, List(Case(App(_, _, _, List(z: Var)), body, _))) = Subst.from(List(c), List(n))(rec): @unchecked
      assert(z != n)
      body ==> Ints.plus(z, n)
      val old = Rec(sum, List(Case(App(sum, List(n)), Ints.plus(n, Old(c)), True)))
      val Rec(_, List(Case(App(_, _, _, List(z_ : Var)), body_, _))) = Old.elim(List(c), List(n), old): @unchecked
      assert(z_ != n)
      body_ ==> Ints.plus(z_, n)

    // the types of the function are substituted, and the recursive calls refer to the function with the new types
    test("types"):
      val a = Param("a")
      val x = Var("x", a)
      val id = Fun("id", Nil, List(x), a)
      val rec = Rec(id, List(Case(App(id, List(x)), App(id, List(x)), True)))
      val su = Subst[Type, Expr](Map(a -> Sort.int), Map())
      val Rec(id_, List(Case(pat, body, _))) = su(rec): @unchecked
      val x_ = Var("x", Sort.int)
      id_.args ==> List(Sort.int)
      id_.res ==> Sort.int
      pat ==> App(id_, List(x_))
      body ==> App(id_, List(x_))
      rec.params ==> Set(a)
      su(rec).params ==> Set()

    // the type parameters of the function are bound, rigid in the cases and instantiated freshly at each use,
    // not substituted, and renamed if they would capture a type parameter of the range
    test("params"):
      val a = Param("a")
      val b = Param("b")
      val x = Var("x", a)
      val id = Fun("id", List(a), List(x), a)
      val ids = Rec(id, List(Case(App(id, List(x)), x, True)))
      ids.params ==> Set()
      Type.check(State.empty, Scope.empty, ids, int) ==> ids
      error(Rec(id, List(Case(App(id, List(x)), Ints.zero, True))), int) ==> "type mismatch"
      Subst[Type, Expr](Map(a -> Sort.int), Map())(ids) ==> ids
      val z = Var("z", b)
      val rec = Rec(id, List(Case(App(id, List(x)), x, Eq(z, z))))
      rec.params ==> Set(b)
      val Rec(id_, List(Case(_, _, Eq(z_ : Var, _)))) = Subst[Type, Expr](Map(b -> a), Map())(rec): @unchecked
      assert(id_.params != List(a))
      z_ ==> Var("z", a)

    // a definition without a match is a single case, an undefined function has no recursive function
    test("definitions"):
      Rec.from(State.empty, sum, Ints.plus(Var("x", Sort.int), Ints.one)) ==>
        Rec(sum, List(Case(App(sum, List(Var("x", Sort.int))), Ints.plus(Var("x", Sort.int), Ints.one), True)))
      val message =
        try
          Rec.from(State.empty, sum)
          ""
        catch case Error(msg, _*) => msg
      message ==> "function not defined"

    // the bodies are simplified assuming their guards, the function is not unfolded
    test("simplify"):
      val body = Ite(Ints.le(n, Ints.zero), Ints.zero, Ints.plus(n, Ints.zero))
      val rec = Rec(sum, List(Case(App(sum, List(n)), body, Ints.le(n, Ints.zero))))
      Simplify.simplify(Config.default, State.empty, Context.empty, rec) ==>
        Rec(sum, List(Case(App(sum, List(n)), Ints.zero, Ints.le(n, Ints.zero))))
