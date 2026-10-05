package cuvee.test
package smtlib

import utest._

object Roundtrip extends TestSuite:
  // printing SMT-LIB examples must be stable when the output is parsed again
  val tests =
    Examples.tests(Examples.find(os.sub, "smt2")): file =>
      val first = os.temp(suffix = ".smt2")
      val second = os.temp(suffix = ".smt2")

      Examples.errors(file.toString, "-o", first.toString) ==> Nil
      Examples.errors(first.toString, "-o", second.toString) ==> Nil
      os.read(second) ==> os.read(first)

// the programs of the Dafny and Boogie examples printed as SMT-LIB can be read back, and printing them again is stable;
// the sorts and datatypes of the preludes of the frontends are not printed (see TODO.md), hence only examples without
object Programs extends TestSuite:
  val prelude = List("tuple", "event", "chan", "seq<", "datatype", "type ")

  def plain(file: os.Path) =
    !prelude.exists(os.read(file).contains)

  val tests =
    Examples.tests((Examples.find(os.sub / "dafny", "dfy") ++ Examples.find(os.sub / "hybrid", "dfy") ++ Examples.find(os.sub / "boogie", "bpl")).filter(plain)): file =>
      val first = os.temp(suffix = ".smt2")
      val second = os.temp(suffix = ".smt2")

      Examples.errors(file.toString, "-print", "smt2", "-o", first.toString) ==> Nil
      Examples.errors(first.toString, "-o", second.toString) ==> Nil
      os.read(second) ==> os.read(first)
