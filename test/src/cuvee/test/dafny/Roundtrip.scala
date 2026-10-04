package cuvee.test
package dafny

import java.io.StringReader

import utest._

import cuvee.dafny.Printer
import cuvee.dafny.Source

object Roundtrip extends TestSuite:
  // printing the internal representation of the Dafny examples must be stable
  // when the output is parsed again, the original file is not compared
  val tests =
    Examples.tests(Examples.find(os.sub / "dafny", "dfy")): file =>
      val (cmds, errors) = Examples.output("-print", "null", file.toString)
      errors ==> Nil

      val first = Printer.lines(cmds)
      val (_, cmds_) = Source(new StringReader(first.mkString("\n")))
      val second = Printer.lines(cmds_.toList.filterNot(Examples.prelude(file.toString).contains))
      second ==> first
