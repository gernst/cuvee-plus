package cuvee.test

import utest._

import cuvee.core._

// the preludes declare the built-in functions exactly as cuvee.core.Fun does,
// including the names of the type parameters a$0, a$1, ... and of the formal parameters x$0, x$1, ...,
// which are written with subscripts in Dafny and Boogie
object Preludes extends TestSuite:
  def init(source: cuvee.pipe.Source): State =
    source(new java.io.StringReader(""))._1

  // the declaration in the prelude, compared with all of its components
  def same(state: State, fun: Fun) =
    val decl = state.funs((fun.name, fun.arity))
    (decl.name, decl.params, decl.formals, decl.res) ==> (fun.name, fun.params, fun.formals, fun.res)

  val core = List(Fun.true_, Fun.false_, Fun.eq_, Fun.ite, Fun.not, Fun.and, Fun.or, Fun.imp)

  val tests = Tests:
    test("smtlib"):
      val state = init(cuvee.smtlib.Source)
      for fun <- core ++ List(Fun.select, Fun.store, Fun.const, Fun.int.div, Fun.int.mod, Fun.real.div) ++ Fun.seq.all
      do same(state, fun)

    test("boogie"):
      val state = init(cuvee.boogie.Source)
      for fun <- core ++ List(Fun.select, Fun.store, Fun.int.div, Fun.int.mod, Fun.real.div)
      do same(state, fun)

    // indexing and updates are generic in Dafny, for arrays and sequences
    test("dafny"):
      val state = init(cuvee.dafny.Source)
      for fun <- core
      do same(state, fun)

    // the generic operators have one type parameter a$0 and are resolved by Overload
    test("generic"):
      for source <- List(cuvee.smtlib.Source, cuvee.boogie.Source, cuvee.dafny.Source)
      do
        val state = init(source)
        for (name, arity) <- Overload.generic if state.funs.contains((name, arity))
        do
          val decl = state.funs((name, arity))
          assert(decl.params.isEmpty || decl.params.head == Param.a)
