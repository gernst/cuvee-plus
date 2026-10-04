package cuvee.test
package transform

import utest._

import cuvee.Error
import cuvee.core._

// the Horn clauses of the Dafny examples have the same result with -flat as without
object FlatHorn extends TestSuite:
  import cuvee.test.dafny.Horn.{expected, differs, skip}

  val tests =
    Examples.tests(Examples.find(os.sub / "vcgen", "dfy").filterNot(file => skip.contains(file.last))): file =>
      val first = os.read.lines(file).head
      val (_, results) = cuvee.Cuvee.run("-chc", "-flat", "-z3", file.toString)
      results.collect { case error: Error => error.msg } ==> Nil
      results.last ==> differs.getOrElse(file.last, expected(first))

object Flat extends TestSuite:
  val file = (Examples.root / "transform" / "flat.smt2").toString

  def output(args: String*): List[Cmd] =
    val (cmds, errors) = Examples.output(args*)
    errors ==> Nil
    cmds

  // the sorts of the bound variables of all assertions
  def bound(cmds: List[Cmd]): List[Type] =
    for
      case Assert(_, _, Bind(_, xs, _), _) <- cmds;
      x <- xs
    yield x.typ

  val pair = Con("Pair", 2)
  val stack = Sort(Con("Stack", 1), List(Sort.int))

  val tests = Tests:
    test("records are flattened in the arguments of predicates"):
      val cmds = output("-flat", "-print", "null", file)
      val p = cmds.collectFirst { case DeclareFun(fun, _) if fun.name.name == "p" => fun }
      p.map(_.args) ==> Some(List(Sort.int, Sort.int, Sort.bool, stack))

    test("bound variables of record sorts are replaced, others are kept"):
      val types = bound(output("-flat", "-print", "null", file))
      assert(types.contains(stack))
      assert(!types.exists { case Sort(`pair`, _) => true; case _ => false })

    test("without -flat"):
      val types = bound(output("-print", "null", file))
      assert(types.exists { case Sort(`pair`, _) => true; case _ => false })

    test("satisfiable"):
      val (_, results) = cuvee.Cuvee.run("-flat", "-z3", file)
      results.last ==> Status.Sat
