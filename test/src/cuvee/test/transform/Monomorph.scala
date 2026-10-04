package cuvee.test
package transform

import utest._

import cuvee.core._

// polymorphic functions are replaced by their instances, which are declared before their first use
object Monomorph extends TestSuite:
  val file = (Examples.root / "transform" / "mono.smt2").toString

  val tests = Tests:
    test("instances"):
      val (cmds, errors) = Examples.output("-monomorph", file)
      errors ==> Nil

      val funs = cmds.collect:
        case DeclareFun(fun, _)   => fun
        case DefineFun(fun, _, _) => fun

      assert(funs.forall(_.params.isEmpty))
      funs.map(_.name.name) ==> List("b", "cons<Int>", "nil<Int>", "single<Int>", "cons<Bool>", "nil<Bool>", "single<Bool>")

    test("solver"):
      val (_, results) = cuvee.Cuvee.run("-monomorph", "-z3", file)
      Examples.status(results) ==> Status.Sat
