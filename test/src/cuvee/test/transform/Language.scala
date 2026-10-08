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
  // the printed output of `args` on count.dfy, as stdout shows it
  def output(args: String*): String =
    Examples.show(args :+ file)
    val (out, _, _) = cuvee.test.Expected.run(args.toList :+ file, java.nio.file.Path.of(file))
    out.mkString("\n")

  def sorts(cmds: List[Cmd]): Set[String] =
    cmds.collect:
      case DeclareSort(con, _)              => con.name.name
      case DeclareDatatypes(List(con), _, _) => con.name.name
    .toSet

  val file = (Examples.root / "dafny" / "language" / "count.dfy").toString

  val tests = Tests:
    test("smt2"):
      val text = output("-print", "smt2")
      val (_, cmds) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader(text))
      val (_, prelude) = Examples.source(cuvee.smtlib.Source, new java.io.StringReader(""))
      val sorts_ = sorts(cmds.toList.filterNot(prelude.contains))
      assert(sorts_.contains("tuple") && sorts_.contains("Bag") && sorts_.contains("Map"))
      assert(!sorts_.contains("Int") && !sorts_.contains("Seq") && !sorts_.contains("Set") && !sorts_.contains("Trace"))

    test("dfy"):
      val text = output()
      assert(!text.contains("tuple₂") && !text.contains("{:dfy}"))

    test("teq"):
      assert(!output("-teq").contains("{:teq}"))
      assert(!output("-teq", "-print", "dfy").contains("{:teq}"))
      assert(!output("-teq", "-print", "smt2").contains(":teq"))
      assert(!output("-print", "smt2", "-teq").contains(":teq"))

    // the declarations that the receiver knows are acknowledged and dropped before it
    test("filter"):
      val buffer = scala.collection.mutable.ListBuffer[Cmd]()
      val a = DeclareSort(Con("A", 0), Attrs(List("dfy" -> None)))
      val b = DeclareSort(Con("B", 0), Attrs.empty)
      val sink = cuvee.pipe.Sink.filter(Set("dfy"), cuvee.pipe.Sink.collect(buffer))
      val (result, _, _) = sink.query(a)
      result ==> Ack.Success
      sink.exec(b)
      buffer.toList ==> List(b)
