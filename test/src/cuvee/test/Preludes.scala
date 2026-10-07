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
      for fun <- core ++ List(Fun.select, Fun.store, Fun.const, Fun.int.div, Fun.int.mod, Fun.real.div) ++ Fun.seq.all ++ Fun.set.all ++ Fun.bag.all ++ Fun.map.all
      do same(state, fun)

    test("boogie"):
      val state = init(cuvee.boogie.Source)
      for fun <- core ++ List(Fun.select, Fun.store, Fun.int.div, Fun.int.mod, Fun.real.div)
      do same(state, fun)

    // the core theory with integers and arrays, including constant arrays, where arithmetic is on Int only
    test("c"):
      val state = init(cuvee.c.Source)
      for fun <- core ++ List(Fun.select, Fun.store, Fun.const) ++ Fun.int.all
      do same(state, fun)

    // indexing and updates are generic in Dafny, for arrays and sequences, and so is negation, for bitvectors
    test("dafny"):
      val state = init(cuvee.dafny.Source)
      for fun <- core.filterNot(_ == Fun.not)
      do same(state, fun)
      assert(Overload.isGeneric(state.funs((Fun.not.name, 1))))

    // the generic operators have one type parameter a$0 and are resolved by Overload
    test("generic"):
      for source <- List(cuvee.smtlib.Source, cuvee.boogie.Source, cuvee.dafny.Source)
      do
        val state = init(source)
        for (name, arity) <- Overload.generic if state.funs.contains((name, arity))
        do
          val decl = state.funs((name, arity))
          assert(decl.params.isEmpty || decl.params.head == Param.a)

    // arithmetic and comparison are generic in Boogie, they are resolved after type checking
    test("overloaded"):
      val state = init(cuvee.boogie.Source)
      for fun <- List(Fun.int.uminus, Fun.int.plus, Fun.int.minus, Fun.int.times, Fun.int.lt, Fun.int.le, Fun.int.gt, Fun.int.ge)
      do assert(Overload.isGeneric(state.funs((fun.name, fun.arity))))

    // indexing, updates, membership, cardinality, merge, and removal of keys on maps
    test("maps"):
      val state = init(cuvee.smtlib.Source)
      val typ = Sort.map(Sort.int, Sort.bool)
      val m = Var("m", typ)
      val n = Var("n", typ)
      val k = Var("k", Sort.int)
      val v = Var("v", Sort.bool)
      val ks = Var("ks", Sort.set(Sort.int))

      def resolve(name: String, args: Expr*) =
        val name_ = _root_.util.Name(name, None)
        // the result type determines the implementation of conversions only
        val impl = Overload.impl(name_, args.length, args(Overload.dispatch(name_, args.length)).typ, Param("r"))
        Overload.app(state, impl.get._2, args.toList)

      resolve("select", m, k) ==> FinMaps.get(m, k)
      resolve("store", m, k, v) ==> FinMaps.store(m, k, v)
      resolve("in", k, m) ==> FinMaps.member(k, m)
      resolve("|_|", m) ==> FinMaps.card(m)
      resolve("+", m, n) ==> FinMaps.update(m, n)
      resolve("-", m, ks) ==> FinMaps.minus(m, ks)
      resolve("<=", m, n) ==> FinMaps.subset(m, n)
