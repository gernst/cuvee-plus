package cuvee.test

import utest._

import cuvee.core._

// old(e) in a single traversal: free variables are replaced by `now`, inside of old by `before`,
// bound variables are kept, and renamed where they would capture a variable of the replacements
object Olds extends TestSuite:
  val g = Var("g", Sort.int)
  val g1 = Var("g1", Sort.int)
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)

  val tests = Tests:
    // the modified variable g has the new value g1 outside of old and keeps its value inside of it
    test("call"):
      val now = Subst[Type, Expr](Map(), Map(g -> g1, x -> y))
      val before = Subst[Type, Expr](Map(), Map(x -> y))
      val phi = Eq(g, Ints.plus(Old(g), x))
      Old.instance(now, before, phi) ==> Eq(g1, Ints.plus(g, y))

    // nested occurrences of old refer to the same values
    test("nested"):
      val before = Subst[Type, Expr](Map(), Map(g -> g1))
      Old.instance(Subst.empty, before, Old(Ints.plus(g, Old(g)))) ==> Ints.plus(g1, g1)
      Old.elim(List(g), List(g1), Eq(g, Old(g))) ==> Eq(g, g1)

    // a bound variable shadows the replaced one, inside of old as well, which is stripped
    test("bound"):
      val before = Subst[Type, Expr](Map(), Map(g -> g1))
      Old.instance(Subst.empty, before, All(List(g), Eq(g, Old(g)))) ==> All(List(g), Eq(g, g))

    // the bound variable g1 would capture the replacement of g inside of old, it is renamed
    test("capture"):
      val before = Subst[Type, Expr](Map(), Map(g -> g1))
      val Bind(_, List(z), body) = Old.instance(Subst.empty, before, All(List(g1), Eq(g1, Old(g)))): @unchecked
      assert(z != g1)
      body ==> Eq(z, g1)

    // the type parameters are instantiated by `now`, also those of bound variables
    test("types"):
      val a = Param("a")
      val p = Var("p", a)
      val now = Subst[Type, Expr](Map(a -> Sort.int), Map())
      Old.instance(now, now, All(List(p), Eq(p, p))) ==> All(List(Var("p", Sort.int)), Eq(Var("p", Sort.int), Var("p", Sort.int)))
