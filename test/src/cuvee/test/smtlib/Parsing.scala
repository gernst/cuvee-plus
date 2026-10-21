package cuvee.test
package smtlib

import utest._
import cuvee.Cuvee

// bitvectors are passed to the solver
object BitVectors extends TestSuite:
  import cuvee.core._

  val tests = Tests:
    test("solver"):
      val file = Examples.root / "smtlib" / "language" / "bitvectors.smt2"
      val results = Examples.answers("-z3", file.toString)
      Examples.status(results) ==> Status.Unsat

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
      message(Ints.minus(Nil)) ==> Some("no arguments")

// the sugar of nested lambdas and arrays
object Lambdas extends TestSuite:
  import cuvee.core._

  val tests = Tests:
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
