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
  val funs = (Examples.root / "transform" / "flat_funs.smt2").toString

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

    // equations x == t of bound variables in the antecedent are inlined, also t == x,
    // those of free variables and those where x occurs in t are kept, as are formulas that are not clauses
    test("equations inlined"):
      val x = Var("x", Sort.int)
      val y = Var("y", Sort.int)
      val z = Var("z", Sort.int)
      val g = Var("g", Sort.int)
      val p = Fun("p", Nil, cuvee.core.Fun.formals(Sort.int, Sort.int), Sort.bool)
      def P(a: Expr, b: Expr) = App(p, List(a, b))
      val f = cuvee.transform.Flat

      f.eliminate(All(List(x, y), Imp(And(Eq(x, Plus.int(y, One.int)), P(x, y)), P(y, x)))) ==>
        All(List(y), Imp(P(Plus.int(y, One.int), y), P(y, Plus.int(y, One.int))))
      f.eliminate(All(List(x, y), Imp(And(P(x, y), Eq(y, x)), P(y, Zero.int)))) ==>
        All(List(x), Imp(P(x, x), P(x, Zero.int)))
      val kept = All(List(z), Imp(And(List(Eq(g, Plus.int(z, One.int)), Eq(z, Plus.int(z, One.int)), P(z, z))), P(g, z)))
      f.eliminate(kept) ==> kept
      f.eliminate(Imp(Eq(x, y), P(x, y))) ==> Imp(Eq(x, y), P(x, y))

    // the equations between the fields of records are inlined
    test("fields inlined"):
      val cmds = output("-flat", "-print", "null", file)
      val bound_ = cmds.collect { case Assert(_, _, All(xs, Imp(ante, _)), _) => (xs.toSet, And.flatten(ante)) }
      for (xs, phis) <- bound_ do
        assert(!phis.exists { case Eq(x: Var, _) => xs.contains(x); case Eq(_, x: Var) => xs.contains(x); case _ => false })

    // the declarations of records are dropped, other datatypes are kept
    test("records dropped"):
      val cmds = output("-flat", "-print", "null", file)
      cmds.collect { case DeclareDatatypes(cons, _, _) => cons.map(_.name.name) } ==> List(List("Stack"))

    // functions take the fields of records, those with records as results are split by the fields,
    // also definitions, whose bodies are split likewise
    test("functions"):
      val cmds = output("-flat", "-print", "null", funs)
      val decls = cmds.collect { case DeclareFun(fun, _) => fun.name.name -> fun.args }
      decls ==> List("origin_fst" -> Nil, "origin_snd" -> Nil, "step_fst" -> List(Sort.int, Sort.int), "step_snd" -> List(Sort.int, Sort.int))

      val defs = cmds.collect { case DefineFun(fun, body, _) => (fun.name.name, fun.args.length, body) }
      defs.map(_._1) ==> List("swap_fst", "swap_snd", "norm")
      defs.map(_._2) ==> List(2, 2, 3)

      // no records remain, in particular no selectors, constructors, testers, or bound variables
      val phis = cmds.collect { case Assert(_, _, phi, _) => phi } ++ defs.map(_._3)
      assert(phis.flatMap(types).forall { case Sort(Con(_root_.util.Name("Pair", _), _), _) => false; case _ => true })

    // ite on records is split by the fields, distinct becomes pairwise disequalities of the fields
    test("ite and distinct"):
      val cmds = output("-flat", "-print", "null", funs)
      val phis = cmds.collect { case Assert(_, _, phi, _) => phi }
      val ex = phis.collectFirst { case Ex(xs, body) => (xs.map(_.name.name), body) }
      val Some((xs, And(conjuncts))) = ex: @unchecked
      xs ==> List("p_fst", "p_snd", "b")
      conjuncts.length ==> 3
      assert(conjuncts.take(2).forall { case Eq(_, Ite(_, _, _)) => true; case _ => false })

    // unsupported: records that instantiate type parameters, also of arrays, and other terms of records
    test("unsupported"):
      val pair = "(declare-datatype Pair ((pair (fst Int) (snd Int))))\n"
      Examples.check("smt2", pair + "(declare-fun p (par (a) (a) Bool))\n(assert (forall ((x Pair)) (p x)))", "-flat") ==>
        List("record instantiates a type parameter")
      Examples.check("smt2", pair + "(declare-fun a () (Array Int Pair))\n(assert (forall ((x Pair)) (= (store a 0 x) a)))", "-flat") ==>
        List("record instantiates a type parameter")
      Examples.check("smt2", pair + "(declare-fun x () Int)\n(assert (= (fst (let ((y (pair x x))) y)) x))", "-flat") ==>
        List("term of a record not supported")

