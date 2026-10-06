package cuvee.test
package transform

import utest._

import cuvee.Error
import cuvee.core._

// the Horn clauses of the Dafny examples have the same result with -flat as without
object FlatHorn extends TestSuite:
  import cuvee.test.dafny.Horn.expected

  val tests =
    Examples.tests(Examples.find(os.sub / "dafny" / "horn", "dfy")): file =>
      val first = os.read.lines(file).head
      val (_, results) = cuvee.Cuvee.run("-chc", "-flat", "-z3", file.toString)
      results.collect { case error: Error => error.msg } ==> Nil
      Examples.status(results) ==> expected(first)

object Flat extends TestSuite:
  val file = (Examples.root / "transform" / "flat.smt2").toString
  val poly = (Examples.root / "transform" / "flat_poly.smt2").toString

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

  // the types of all subexpressions, including the instances of the functions
  def types(expr: Expr): List[Type] =
    expr match
      // conjunctions are flattened, since the printer collapses them and the parser nests them to the left
      case And(phis)               => Sort.bool :: phis.flatMap(types)
      case App(_, inst, typ, args) => inst ++ (typ :: args.flatMap(types))
      case Bind(_, xs, body)       => xs.map(_.typ) ++ types(body)
      case _                       => List(expr.typ)

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
      Examples.status(results) ==> Status.Sat

    // the parameters of the datatypes are instantiated, also those that do not occur in the fields
    test("polymorphic predicates"):
      val cmds = output("-flat", "-print", "null", poly)
      val q = cmds.collectFirst { case DeclareFun(fun, _) if fun.name.name == "q" => fun }
      q.map(_.args) ==> Some(List(Param("a"), Sort.int))

      // the types inside the flattened assertions are those found by the type checker when they are parsed again,
      // the formal parameters of the predicates are named differently
      val printed = cuvee.smtlib.Printer.lines(cmds).mkString("\n")
      val (_, cmds_) = cuvee.smtlib.Source(new java.io.StringReader(printed))
      val phis = cmds.collect { case Assert(_, _, phi, _) => phi }
      val phis_ = cmds_.toList.collect { case Assert(_, _, phi, _) => phi }
      phis_.flatMap(types) ==> phis.flatMap(types)
