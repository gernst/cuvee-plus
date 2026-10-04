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

    // inside of the combinators of trace equation systems
    test("combinators"):
      val text = "(declare-sort Lst 1)\n(declare-fun single (par (a) (a) (Lst a)))\n(declare-const J (Seq Int))\n" +
        "(assert (= (map ((j J)) (single j)) (map ((j J)) (single (+ j 0)))))"
      val tmp = os.temp(text, suffix = ".smt2")
      val (cmds, errors) = Examples.output("-monomorph", tmp.toString)
      errors ==> Nil
      cmds.collect { case DeclareFun(fun, _) => fun.name.name } ==> List("J", "single<Int>")

    test("solver"):
      val (_, results) = cuvee.Cuvee.run("-monomorph", "-z3", file)
      Examples.status(results) ==> Status.Sat
