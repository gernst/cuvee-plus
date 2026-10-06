package cuvee.test
package transform

import utest._

import cuvee.core._

// the declarations of the preludes that are part of the language of the output are dropped:
// Dafny printed as SMT-LIB declares the tuples and the containers of Dafny other than sequences, but not Int,
// Dafny printed as Dafny none of these
object Language extends TestSuite:
  def output(args: String*): List[Cmd] =
    val buffer = scala.collection.mutable.ListBuffer[Cmd]()
    cuvee.Cuvee.run(args.toList, List(cuvee.pipe.Sink.collect(buffer)))
    buffer.toList

  def sorts(cmds: List[Cmd]): Set[String] =
    cmds.collect:
      case DeclareSort(con, _)              => con.name.name
      case DeclareDatatypes(List(con), _, _) => con.name.name
    .toSet

  val file = (Examples.root / "dafny" / "count.dfy").toString

  val tests = Tests:
    test("smt2"):
      val sorts_ = sorts(output("-print", "null", "-print", "smt2", file))
      assert(sorts_.contains("tuple2") && sorts_.contains("Set") && sorts_.contains("Map"))
      assert(!sorts_.contains("Int") && !sorts_.contains("Seq") && !sorts_.contains("Trace"))

    test("dfy"):
      sorts(output("-print", "null", file)) ==> Set()
