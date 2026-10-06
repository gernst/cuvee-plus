package cuvee.test
package boogie

import java.io.StringReader

import utest._

import cuvee.Error
import cuvee.core._
import cuvee.boogie.Printer
import cuvee.boogie.Source

// printing the internal representation of the Boogie examples must be stable
// when the output is parsed again, the original file is not compared
object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "boogie", "bpl")): file =>
      val args = List("-print", "null", file.toString)
      val (cmds, errors) = Examples.output(args*)
      errors ==> Nil

      val first = Printer.lines(cmds)
      val (_, cmds_) = Source(new StringReader(first.mkString("\n")))
      val second = Printer.lines(cmds_.toList.filterNot(Examples.prelude(args*).contains))
      second ==> first

object Printing extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val zero = Lit(BigInt(0), Sort.int)
  val p = Var("p", Sort.bool)
  val q = Var("q", Sort.bool)
  val a = Var("a", Sort.array(Sort.int, Sort.int))

  // the printer ignores types, chains with more than two arguments do not match the signatures
  def app(fun: Fun, args: Expr*) =
    App(fun, Nil, fun.res, args.toList)

  def expr(expr: Expr) =
    Printer.lines(expr).mkString(" ")

  def prog(prog: Prog) =
    Printer.lines(prog)

  def error(body: => Any): String =
    try
      body
      "no error"
    catch case Error(msg, _*) => msg

  val tests = Tests:
    test("types"):
      Printer.lines(Sort.array(Sort.int, Sort.array(Sort.bool, Sort.int))) ==> List("[int][bool]int")
      Printer.lines(Sort(Con("Stack", 1), List(Param("a")))) ==> List("Stack<a>")

    test("specs"):
      prog(Spec.assume(Lt.int(x, y))) ==> List("assume x < y;")
      prog(Spec.assert(Lt.int(x, y))) ==> List("assert x < y;")
      prog(Spec.havoc(List(x, y))) ==> List("havoc x, y;")
      prog(Spec(List(x), Lt.int(zero, x), Lt.int(x, y))) ==>
        List("assert 0 < x;", "havoc x;", "assume x < y;")

    test("assign and call"):
      prog(Assign(List(x, y), List(y, x))) ==> List("x, y := y, x;")
      prog(Assign(List(a), List(Store(a, x, Select(a, y))))) ==> List("a := a[x := a[y]];")
      prog(Call("p", List(x), Nil)) ==> List("call p(x);")
      prog(Call("p", List(x), List(y))) ==> List("call y := p(x);")

    test("choice"):
      val progs = List(Assign(List(x), List(zero)), Assign(List(x), List(y)))
      prog(Choice(progs)) ==> List("if (*) {", "  x := 0;", "} else {", "  x := y;", "}")

    test("else if"):
      val prog_ = If(Lt.int(x, y), Break, If(Lt.int(y, x), Return, Block(Nil, Nil)))
      prog(prog_) ==> List("if (x < y) {", "  break;", "} else if (y < x) {", "  return;", "}")

    // continue is not Boogie, but part of the dialect
    test("continue"):
      prog(While(Lt.int(x, y), Block(Nil, List(Continue)), cuvee.core.Attrs(Nil))) ==>
        List("while (x < y) {", "  continue;", "}")

    test("loop"):
      val attrs = cuvee.core.Attrs(List("invariant" -> Some(Le.int(x, y)), "modifies" -> Some(List(a))))
      prog(While(Lt.int(x, y), Block(Nil, Nil), attrs)) ==>
        List("while (x < y)", "  invariant x <= y;", "  modifies a;", "{}")

    test("iter"):
      val attrs = cuvee.core.Attrs(List("invariant" -> Some(Le.int(x, y))))
      prog(Iter(Assign(List(x), List(y)), attrs)) ==>
        List("while (*)", "  invariant x <= y;", "{", "  x := y;", "}")

    test("unsupported"):
      val other = cuvee.core.Attrs(List("other" -> Some(x)))
      error(prog(While(True, Block(Nil, Nil), other))) ==> "attributes of loops not supported in Boogie"

    // the components of a termination measure are a single clause
    test("decreases"):
      val dec = cuvee.core.Attrs(List("decreases" -> Some(x), "decreases" -> Some(y)))
      prog(While(True, Block(Nil, Nil), dec)) ==> List("while (true)", "  decreases x, y;", "{}")

    test("mixfix"):
      expr(Plus.int(Plus.int(x, y), zero)) ==> "x + y + 0"
      expr(Plus.int(x, Plus.int(y, zero))) ==> "x + (y + 0)"
      expr(Times.int(Plus.int(x, y), Minus.int(x, y))) ==> "(x + y) * (x - y)"
      expr(Imp(p, Imp(q, p))) ==> "p ==> q ==> p"
      expr(Imp(Imp(p, q), p)) ==> "(p ==> q) ==> p"
      expr(And(Or(p, q), Lt.int(x, y))) ==> "(p || q) && x < y"

    test("disequalities and chains"):
      expr(Not(Eq(x, y))) ==> "x != y"
      expr(Not(And(p, q))) ==> "!(p && q)"
      expr(Distinct(List(x, y))) ==> "x != y"
      expr(Distinct(List(x, y, zero))) ==> "x != y && x != 0 && y != 0"
      expr(app(Fun.int.lt, x, y, zero)) ==> "x < y && y < 0"

    test("quantifiers and conditionals"):
      expr(And(All(List(x), Lt.int(x, y)), p)) ==> "(forall x: int :: x < y) && p"
      expr(Plus.int(Ite(p, x, y), zero)) ==> "(if p then x else y) + 0"
      expr(Let(List(x), List(y), Plus.int(x, x))) ==> "y + y"
