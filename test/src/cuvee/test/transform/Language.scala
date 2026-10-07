package cuvee.test
package transform

import utest._

import _root_.util.Name

import cuvee.core._

// the printers drop the declarations of the preludes that are part of the language of the output:
// Dafny printed as SMT-LIB declares the tuples and the containers of Dafny other than sequences and sets, but not Int,
// Dafny printed as Dafny none of these;
// the features added by -teq are part of the languages of the input and of the output, regardless of -print
object Language extends TestSuite:
  // the printed output, written with -o
  def output(args: String*): String =
    val file = os.temp(suffix = ".out")
    cuvee.Cuvee.run(List("-o", file.toString) ++ args)
    os.read(file)

  def sorts(cmds: List[Cmd]): Set[String] =
    cmds.collect:
      case DeclareSort(con, _)              => con.name.name
      case DeclareDatatypes(List(con), _, _) => con.name.name
    .toSet

  val file = (Examples.root / "dafny" / "language" / "count.dfy").toString

  val tests = Tests:
    test("smt2"):
      val text = output("-print", "smt2", file)
      val (_, cmds) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader(text))
      val (_, prelude) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader(""))
      val sorts_ = sorts(cmds.toList.filterNot(prelude.contains))
      assert(sorts_.contains("tuple") && sorts_.contains("Bag") && sorts_.contains("Map"))
      assert(!sorts_.contains("Int") && !sorts_.contains("Seq") && !sorts_.contains("Set") && !sorts_.contains("Trace"))

    test("dfy"):
      val text = output(file)
      assert(!text.contains("tuple₂") && !text.contains("{:dfy}"))

    test("teq"):
      assert(!output("-teq", file).contains("{:teq}"))
      assert(!output("-teq", "-print", "dfy", file).contains("{:teq}"))
      assert(!output("-teq", "-print", "smt2", file).contains(":teq"))
      assert(!output("-print", "smt2", "-teq", file).contains(":teq"))

    test("filter"):
      val printer = cuvee.pipe.Printer.filter(Set("dfy"), cuvee.pipe.Printer.default)
      val a = DeclareSort(Con("A", 0), Attrs(List("dfy" -> None)))
      val b = DeclareSort(Con("B", 0), Attrs.empty)
      printer.lines(List[Cmd](a, b)) ==> List(b.toString)
