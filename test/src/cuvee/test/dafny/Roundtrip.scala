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
      val args = List("-print", "null") ++ Examples.options(file) :+ file.toString
      val (cmds, errors) = Examples.output(args*)
      errors ==> Nil

      val first = Printer.lines(cmds)
      val config = cuvee.Config.parse(cuvee.Config.default, args)
      val (_, cmds_) = Source(new StringReader(first.mkString("\n")), config)
      val second = Printer.lines(cmds_.toList.filterNot(Examples.prelude(args*).contains))
      second ==> first
