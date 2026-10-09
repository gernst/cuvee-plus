package cuvee.test
package simplify

import utest._

import cuvee.core._
import cuvee.simplify.Fuse as F
import _root_.util.Name

// fixpoint fusion of two recursive functions on lists of integers into one, g(f(xs), ys) as h(xs, ys)
object Fuse extends TestSuite:
  val name = Name("List", None)
  val list = Sort(Con(name, 0), Nil)
  val nil = Fun("nil", Nil, Nil, list)
  val cons = Fun("cons", Nil, List(Var("head", Sort.int), Var("tail", list)), list)
  val head = Fun("head", Nil, List(Var("x", list)), Sort.int)
  val tail = Fun("tail", Nil, List(Var("x", list)), list)
  val data = Datatype(Nil, List(nil -> Nil, cons -> List(head, tail)))
  val state = State.empty.declare(name, 0, Attrs.empty).declare(data).define(name, data)

  val xs = Var("xs", list)
  val ys = Var("ys", list)
  val y = Var("y", Sort.int)
  val k = Var("k", Sort.int)
  val empty = App(nil, Nil)

  // dbl(nil) = nil, dbl(cons(y, ys)) = cons(y + y, dbl(ys))
  val dbl = Fun("dbl", Nil, List(xs), list)
  val dbls =
    Rec(
      dbl,
      List(
        Case(App(dbl, List(empty)), empty, True),
        Case(App(dbl, List(App(cons, List(y, ys)))), App(cons, List(Ints.plus(y, y), App(dbl, List(ys)))), True)
      )
    )

  // sum(nil) = 0, sum(cons(y, ys)) = y + sum(ys)
  val sum = Fun("sum", Nil, List(xs), Sort.int)
  val sums =
    Rec(
      sum,
      List(
        Case(App(sum, List(empty)), Ints.zero, True),
        Case(App(sum, List(App(cons, List(y, ys)))), Ints.plus(y, App(sum, List(ys))), True)
      )
    )

  val tests = Tests:
    // the sum of the doubled list in a single recursion, which constructs no intermediate list
    test("sum"):
      val h = F(state, sums, dbls)
      val Rec(hf, _) = h: @unchecked
      h ==> Rec(
        hf,
        List(
          Case(F.call(hf, List(empty)), Ints.zero, True),
          Case(F.call(hf, List(App(cons, List(y, ys)))), Ints.plus(Ints.plus(y, y), F.call(hf, List(ys))), True)
        )
      )
      Type.check(state, Scope.empty, h, Arrow(List(list), Sort.int)) ==> h

    // the further argument k of the consumer is passed on, its guard is tested before the next case
    test("guards"):
      val take = Fun("take", Nil, List(xs, k), Sort.int)
      val takes =
        Rec(
          take,
          List(
            Case(App(take, List(empty, k)), Ints.zero, True),
            Case(
              App(take, List(App(cons, List(y, ys)), k)),
              Ints.plus(y, App(take, List(ys, Ints.minus(k, Ints.one)))),
              Ints.lt(Ints.zero, k)
            ),
            Case(App(take, List(App(cons, List(y, ys)), k)), Ints.zero, True)
          )
        )
      val h = F(state, takes, dbls)
      val Rec(hf, _) = h: @unchecked
      val List(_, k_) = hf.formals: @unchecked
      h ==> Rec(
        hf,
        List(
          Case(F.call(hf, List(empty, k_)), Ints.zero, True),
          Case(
            F.call(hf, List(App(cons, List(y, ys)), k_)),
            Ite(Ints.lt(Ints.zero, k_), Ints.plus(Ints.plus(y, y), F.call(hf, List(ys, Ints.minus(k_, Ints.one)))), Ints.zero),
            True
          )
        )
      )
      Type.check(state, Scope.empty, h, Arrow(List(list, Sort.int), Sort.int)) ==> h

    // the result xs of the producer has no constructor, the consumer is applied as a function value
    test("undecided"):
      val id = Fun("id", Nil, List(xs), list)
      val ids = Rec(id, List(Case(App(id, List(xs)), xs, True)))
      val h = F(state, sums, ids)
      val Rec(hf, _) = h: @unchecked
      h ==> Rec(hf, List(Case(F.call(hf, List(xs)), Apply(sums, List(xs)), True)))

    // definitions with a match on a parameter as recursive functions, here those of sum and dbl above,
    // where the matched parameter in a body is the pattern, and the variables of a pattern shadow the other parameters
    test("definitions"):
      val sumBody =
        Match(xs, List(Case(empty, Ints.zero, True), Case(App(cons, List(y, ys)), Ints.plus(y, App(sum, List(ys))), True)))
      val dblBody =
        Match(
          xs,
          List(Case(empty, xs, True), Case(App(cons, List(y, ys)), App(cons, List(Ints.plus(y, y), App(dbl, List(ys)))), True))
        )
      Rec.from(state, sum, sumBody) ==> sums
      Rec.from(state, dbl, dblBody) ==> dbls
      val state_ = state.declare(sum.name, Nil, sum.formals, sum.res, Attrs.empty).define(sum.name, 1, sumBody)
      Rec.from(state_, sum) ==> sums

      val first = Fun("first", Nil, List(xs, y), Sort.int)
      val firstBody = Match(xs, List(Case(empty, y, True), Case(App(cons, List(y, ys)), y, True)))
      val Rec(_, List(Case(pat1, body1, _), Case(App(_, _, _, List(pat2, y_ : Var)), body2, _))) =
        Rec.from(state, first, firstBody): @unchecked
      pat1 ==> F.call(first, List(empty, y))
      body1 ==> y
      pat2 ==> App(cons, List(y, ys))
      assert(y_ != y)
      body2 ==> y

