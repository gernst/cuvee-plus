package cuvee.test
package boogie

import utest._

import cuvee.boogie.Scanner
import cuvee.boogie.Grammar

// Boogie examples must be accepted by the grammar
object Grammar extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub, "bpl")): file =>
      val reader = new java.io.FileReader(file.toIO)
      try cuvee.boogie.Grammar.script.parseAll(new Scanner(reader).input)
      catch
        case easyparse.Fail(in, from) =>
          throw new java.lang.AssertionError("parse error in " + from.mkString(", ") + " at " + in.take(10).map(_.text).mkString(" "))
      finally reader.close()
