package cuvee.test
package smtlib

import utest._

object Parsing extends TestSuite:
  // SMT-LIB examples must parse without errors
  val tests =
    Examples.tests(Examples.find(os.sub, "smt2")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

// a doubled "" inside a string stands for " (SMT-LIB 2.6)
object Strings extends TestSuite:
  import cuvee.core._

  val tests = Tests:
    test("escape"):
      val (_, cmds) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader("(assert (= \"a\"\"b\" \"\"))"))
      val Assert(_, _, Eq(Lit(left, _), Lit(right, _)), _) = cmds.last: @unchecked
      (left, right) ==> ("a\"b", "")
      cuvee.smtlib.Printer.lines(Lit("a\"b", Sort.string)) ==> List("\"a\"\"b\"")

// bitvectors, whose functions are instantiated for the widths of their arguments
object BitVectors extends TestSuite:
  import cuvee.core._

  def expr(text: String): Expr =
    val (_, cmds) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader("(declare-const x (_ BitVec 8))\n(assert (= " + text + " " + text + "))"))
    val Assert(_, _, Eq(left, _), _) = cmds.last: @unchecked
    left

  def errors(text: String) =
    Examples.check("smt2", "(declare-const x (_ BitVec 8))\n(assert " + text + ")")

  val tests = Tests:
    test("literals"):
      expr("#xff") ==> Lit(BigInt(255), BitVec(8))
      expr("#b101") ==> Lit(BigInt(5), BitVec(3))
      expr("(_ bv5 16)") ==> Lit(BigInt(5), BitVec(16))

    test("widths"):
      expr("(concat x #b1)").typ ==> BitVec(9)
      expr("((_ extract 3 0) x)").typ ==> BitVec(4)
      expr("((_ repeat 3) x)").typ ==> BitVec(24)
      expr("(bvcomp x x)").typ ==> BitVec(1)

    test("errors"):
      errors("(= (bvadd x #b1) x)") ==> List("invalid application of bitvector function")
      errors("(= ((_ extract 8 0) x) x)") ==> List("invalid application of bitvector function")

    test("solver"):
      val file = Examples.root / "smtlib" / "bitvectors.smt2"
      val (_, results) = cuvee.Cuvee.run("-z3", file.toString)
      Examples.status(results) ==> Status.Unsat

// exceptions other than cuvee.Error are reported as internal errors, which stop the run
object Internal extends TestSuite:
  val tests = Tests:
    test("reported"):
      Examples.check("smt2", "(push 99999999999999999999999)\n(check-sat)") ==> List("internal error")

// malformed answers of solvers and malformed applications of sugar are errors, not internal errors
object Malformed extends TestSuite:
  import cuvee.core._
  import cuvee.sexpr.{Id, Str}

  def message(f: => Any) =
    try { f; None }
    catch case error: cuvee.Error => Some(error.msg)

  val tests = Tests:
    test("labels"):
      cuvee.smtlib.Parser.labels(List(Id("labels"), Id("a"))) ==> Labels(List("a"))
      message(cuvee.smtlib.Parser.labels(List(Id("labels"), Str("a")))) ==> Some("invalid label")

    // errors of the solver are raised, which the pipe reports
    test("solver errors"):
      val error = List(Id("error"), Str("oops"))
      message(cuvee.smtlib.Parser.ack(error)) ==> Some("solver error")
      message(cuvee.smtlib.Parser.issat(error)) ==> Some("solver error")
      message(cuvee.smtlib.Parser.labels(error)) ==> Some("solver error")

    // associative operators have no neutral element
    test("no arguments"):
      message(Minus.int(Nil)) ==> Some("no arguments")

// lambdas are arrays of a single index, which Dafny cannot print
object Lambdas extends TestSuite:
  import cuvee.core._

  val tests = Tests:
    test("array"):
      val (_, cmds) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader("(assert (= (select (lambda ((x Int)) (+ x 1)) 0) 1))"))
      val Assert(_, _, Eq(App(_, _, _, List(lam: Lam, _)), _), _) = cmds.last: @unchecked
      lam.typ ==> Sort.array(Sort.int, Sort.int)

    // multi-index arrays of SMT-LIB are not curried, unlike the maps of several indices of Boogie
    test("several variables"):
      Examples.check("smt2", "(assert (= (lambda ((x Int) (y Int)) x) (lambda ((x Int) (y Int)) y)))") ==>
        List("lambda of several variables not supported")
      Examples.check("bpl", "axiom (lambda x: int, y: int :: x)[0, 1] == 0;") ==> Nil

    // lambdas are arrays also when function types are declared, since solvers support lambdas of array type only
    test("not functions"):
      Examples.check("smt2", "(declare-const f (-> Int Int)) (assert (= f (lambda ((x Int)) x)))") ==> List("type mismatch")

    // the sugar of nested lambdas and arrays collects all of them
    test("sugar"):
      val x = Var("x", Sort.int)
      val y = Var("y", Sort.bool)
      val typ = Arrays(List(Sort.int, Sort.bool), Sort.int)
      typ ==> Sort.array(Sort.int, Sort.array(Sort.bool, Sort.int))
      val Arrays(indices, value) = typ: @unchecked
      (indices, value) ==> (List(Sort.int, Sort.bool), Sort.int)

      val lam = Lams(List(x, y), x)
      lam.typ ==> typ
      val Lams(bound, body) = lam: @unchecked
      (bound, body) ==> (List(x, y), x)

      val m = Var("m", typ)
      val Arrays.select(base, args) = Arrays.select(m, List(x, y)): @unchecked
      (base, args) ==> (m, List(x, y))
      val Arrays.store(base_, args_, value_) = Arrays.store(m, List(x, y), x): @unchecked
      (base_, args_, value_) ==> (m, List(x, y), x)

    test("dafny"):
      val file = os.temp("(assert (= (lambda ((x Int)) x) (lambda ((y Int)) y)))", suffix = ".smt2")
      Examples.errors("-print", "dfy", file.toString) ==> List("lambda of array type not supported in Dafny")

// function types (-> A B C) and applications (@ f a b) of SMT-LIB 2.7, of the sorts arrow$n and the functions apply$n
// of the prelude (see Arrow and Apply)
object Functions extends TestSuite:
  import cuvee.core._

  def parse(text: String) =
    val (_, cmds) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader(text))
    cmds

  val tests = Tests:
    test("types"):
      val cmds = parse("(declare-const f (-> Int Bool Int))")
      val DeclareFun(f, _) = cmds.last: @unchecked
      f.res ==> Arrow(List(Sort.int, Sort.bool), Sort.int)

    test("applications"):
      val cmds = parse("(declare-const f (-> Int Bool Int)) (assert (= (@ f 1 true) 2))")
      val Assert(_, _, Eq(Apply(_, args), _), _) = cmds.last: @unchecked
      args ==> List(Lit(BigInt(1), Sort.int), True)

    // a function of fewer arguments is applied to the first ones, and its result to the rest
    test("left associative"):
      val cmds = parse("(declare-const g (-> Int (-> Int Int))) (assert (= (@ g 1 2) 0))")
      val Assert(_, _, Eq(Apply(Apply(_, List(a)), List(b)), _), _) = cmds.last: @unchecked
      (a, b) ==> (Lit(BigInt(1), Sort.int), Lit(BigInt(2), Sort.int))

    test("errors"):
      Examples.check("smt2", "(declare-const f (-> Int Int)) (assert (= (@ f true) 0))") ==> List("type mismatch")
      Examples.check("smt2", "(declare-const f Int) (assert (= (@ f 1) 0))") ==> List("type mismatch")

    test("printing"):
      val cmds = parse("(declare-const f (-> Int Bool Int)) (assert (= (@ f 1 true) 2))")
      cuvee.smtlib.Printer.lines(cmds.init.last) ==> List("(declare-const f (-> Int Bool Int))", "")
      cuvee.smtlib.Printer.lines(cmds.last) ==> List("(assert (= (@ f 1 true) 2))", "")
