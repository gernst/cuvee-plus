package cuvee.test

import utest._

import cuvee.Error
import cuvee.core._
import cuvee.sexpr.Attrs

// checks goals, lemmas, and axioms directly against the solver sink with z3
object Solver extends TestSuite:
  val x = Fun("x", Nil, Nil, Sort.int)
  val x_ = App(x, Nil)

  // the solver is stopped even if a check fails
  def run(cmds: Cmd*): Unit =
    val solver = cuvee.smtlib.Solver.z3()
    try
      val sink = cuvee.smtlib.Solver.sink(solver)
      sink.exec(DeclareFun(x, Attrs.empty) :: cmds.toList)
    finally solver.destroy()

  val tests = Tests:
    test("valid lemma"):
      run(Assert(Lemma, Nil, Eq(x_, x_), Attrs.empty))

    test("invalid lemma"):
      val error = assertThrows[Error]:
        run(Assert(Lemma, Nil, Eq(x_, Zero), Attrs.empty))
      error.msg ==> "lemma does not hold"

    test("invalid goal"):
      val error = assertThrows[Error]:
        run(Assert(Goal, Nil, Eq(x_, Zero), Attrs.empty))
      error.msg ==> "goal does not hold"

    test("goal from axiom"):
      run(
        Assert(Axiom, Nil, Eq(x_, One), Attrs.empty),
        Assert(Lemma, Nil, Lt(Zero, x_), Attrs.empty),
        Assert(Goal, Nil, Lt(Zero, x_), Attrs.empty)
      )
