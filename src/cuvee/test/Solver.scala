package cuvee.test

import util.Main
import cuvee.core._
import cuvee.sexpr.Attrs

// checks goals, lemmas, and axioms directly against the solver sink with z3
object Solver extends Main with Tests:
  def main(args: Array[String]) =
    tests("solver sink"):
      val x = Fun("x", Nil, Nil, Sort.int)
      val x_ = App(x, Nil)

      // the solver is stopped even if a check fails
      def run(cmds: Cmd*) =
        val solver = cuvee.smtlib.Solver.z3()
        try
          val sink = cuvee.smtlib.Solver.sink(solver)
          sink.exec(DeclareFun(x, Attrs.empty) :: cmds.toList)
        finally solver.destroy()

      test("valid lemma"):
        run(Assert(Lemma, Nil, Eq(x_, x_), Attrs.empty))

      test("invalid lemma"):
        Check.fails("lemma does not hold"):
          run(Assert(Lemma, Nil, Eq(x_, Zero), Attrs.empty))

      test("invalid goal"):
        Check.fails("goal does not hold"):
          run(Assert(Goal, Nil, Eq(x_, Zero), Attrs.empty))

      test("goal from axiom"):
        run(
          Assert(Axiom, Nil, Eq(x_, One), Attrs.empty),
          Assert(Lemma, Nil, Lt(Zero, x_), Attrs.empty),
          Assert(Goal, Nil, Lt(Zero, x_), Attrs.empty)
        )
