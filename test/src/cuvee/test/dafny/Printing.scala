package cuvee.test
package dafny

import utest._

import cuvee.core._
import cuvee.dafny.Printer

object Printing extends TestSuite:
  val x = Var("x", Sort.int)
  val y = Var("y", Sort.int)
  val zero = Lit(BigInt(0), Sort.int)
  val p = Var("p", Sort.bool)
  val q = Var("q", Sort.bool)

  // the printer ignores types, chains with more than two arguments do not match the signatures
  def app(fun: Fun, args: Expr*) =
    App(fun, Nil, fun.res, args.toList)

  def expr(expr: Expr) =
    Printer.lines(expr).mkString(" ")

  val tests = Tests:
    test("assign"):
      Printer.lines(Assign(List(x, y), List(y, x))) ==> List("x, y := y, x;")

    test("specs"):
      Printer.lines(Spec.assume(App(Fun.int.lt, List(x, y)))) ==> List("assume x < y;")
      Printer.lines(Spec.havoc(List(x, y))) ==> List("havoc x, y;")
      Printer.lines(Spec(List(x), App(Fun.int.lt, List(zero, x)), App(Fun.int.lt, List(x, y)))) ==>
        List("spec x requires 0 < x ensures x < y;")

    test("choice"):
      val progs = List(Assign(List(x), List(zero)), Assign(List(x), List(y)))
      Printer.lines(Choice(progs)) ==> List("if * {", "  x := 0;", "} else {", "  x := y;", "}")

    test("else if"):
      val prog = If(App(Fun.int.lt, List(x, y)), Break, If(App(Fun.int.lt, List(y, x)), Continue, Block(Nil, Nil)))
      Printer.lines(prog) ==> List("if x < y {", "  break;", "} else if y < x {", "  continue;", "}")

    test("iter"):
      val attrs = cuvee.core.Attrs(List("invariant" -> Some(App(Fun.int.le, List(x, y)))))
      Printer.lines(Iter(Assign(List(x), List(y)), attrs)) ==>
        List("while *", "  invariant x <= y", "{", "  x := y;", "}")

    // the right hand sides are in parentheses if they contain a conjunction
    test("ode"):
      val dom = app(Fun.int.le, zero, x)
      val inv = cuvee.core.Attrs(List("invariant" -> Some(app(Fun.int.le, x, y))))
      val t = Var("t", Sort.real)
      Printer.lines(Ode(t, List(x, y), List(y, app(Fun.int.uminus, x)), True, cuvee.core.Attrs.empty)) ==>
        List("ode t :: x', y' == y, -x;")
      Printer.lines(Ode(t, List(p), List(app(Fun.and, p, q)), dom, inv)) ==>
        List("ode t :: p' == (p && q) && 0 <= x", "  invariant x <= y;")

    test("diff"):
      expr(Diff(List(x), x)) ==> "(x :: x)'"
      expr(Diff(List(x, y), app(Fun.int.times, x, y))) ==> "(x, y :: x * y)'"
      expr(app(Fun.int.uminus, Diff(List(x), x))) ==> "-(x :: x)'"

    // real literals have a decimal point, fractions without finite decimal expansion are divisions
    test("real literals"):
      val real = (r: _root_.util.Rational) => Lit(r, Sort.real)
      expr(real(_root_.util.Rational(2))) ==> "2.0"
      expr(real(_root_.util.Rational(-3, 2))) ==> "-1.5"
      expr(real(_root_.util.Rational(1, 3))) ==> "1.0 / 3.0"
      expr(real(_root_.util.Rational(-1, 3))) ==> "-1.0 / 3.0"
      expr(app(Fun.real.times, real(_root_.util.Rational(1, 3)), x)) ==> "1.0 / 3.0 * x"
      expr(app(Fun.real.times, x, real(_root_.util.Rational(1, 3)))) ==> "x * (1.0 / 3.0)"

    // sequence literals are concatenations of units, + and <= are overloaded, x in s is containment of [x]
    test("sequences"):
      val s = Var("s", Sort.seq(Sort.int))
      val one = Lit(BigInt(1), Sort.int)
      val unit = (e: Expr) => app(Fun.seq.unit, e)
      expr(app(Fun.seq.empty)) ==> "[]"
      expr(app(Fun.seq.concat, unit(x), unit(y))) ==> "[x, y]"
      expr(app(Fun.seq.concat, s, unit(x))) ==> "s + [x]"
      expr(app(Fun.seq.prefixof, unit(x), s)) ==> "[x] <= s"
      expr(app(Fun.seq.contains, s, unit(x))) ==> "x in s"
      expr(app(Fun.seq.len, s)) ==> "|s|"
      expr(app(Fun.seq.nth, s, zero)) ==> "s[0]"
      expr(app(Fun.seq.update, s, zero, unit(x))) ==> "s[0 := x]"
      expr(app(Fun.seq.extract, s, one, app(Fun.int.minus, x, one))) ==> "s[1..x]"
      expr(app(Fun.seq.extract, s, zero, x)) ==> "s[0..x]"

    // the parser reads a != b as !(a == b)
    test("disequality"):
      expr(Not(Eq(x, y))) ==> "x != y"
      expr(Not(Eq(p, Not(Eq(x, y))))) ==> "p != (x != y)"
      expr(Not(And(p, q))) ==> "!(p && q)"

    // testers on variables, annotations bind tighter than operators but are no operands of accesses
    test("datatypes"):
      val Seq = Sort.seq(Sort.int)
      val s = Var("s", Seq)
      val nil = Fun("nil", Nil, Nil, Seq)
      expr(Is(s, nil)) ==> "s.nil?"
      expr(app(Fun.int.plus, As(x, Sort.int), y)) ==> "x as int + y"
      expr(app(Fun.seq.nth, As(s, Seq), zero)) ==> "(s as seq<int>)[0]"

    test("mixfix"):
      expr(app(Fun.int.plus, app(Fun.int.plus, x, y), zero)) ==> "x + y + 0"
      expr(app(Fun.int.plus, x, app(Fun.int.plus, y, zero))) ==> "x + (y + 0)"
      expr(app(Fun.int.plus, x, y, zero)) ==> "x + y + 0"
      expr(app(Fun.int.times, app(Fun.int.plus, x, y), app(Fun.int.minus, x, y))) ==> "(x + y) * (x - y)"
      expr(app(Fun.int.minus, x, app(Fun.int.times, y, Lit(BigInt(-1), Sort.int)))) ==> "x - y * -1"
      expr(app(Fun.imp, p, app(Fun.imp, q, p))) ==> "p ==> q ==> p"
      expr(app(Fun.imp, app(Fun.imp, p, q), p)) ==> "(p ==> q) ==> p"
      expr(app(Fun.and, app(Fun.or, p, q), app(Fun.int.lt, x, y))) ==> "(p || q) && x < y"

    test("mixfix non-associative"):
      expr(app(Fun.eq_, app(Fun.int.lt, x, y), p)) ==> "(x < y) == p"
      expr(app(Fun.eq_, p, app(Fun.eq_, q, p))) ==> "p == (q == p)"
      expr(app(Fun.eq_, x, y, zero)) ==> "==(x, y, 0)"

    // the operators inside of parentheses are indented beyond the opening parenthesis
    test("parentheses align"):
      val long = (1 to 8).map(i => app(Fun.int.lt, x, Lit(BigInt(1000000 * i), Sort.int))).reduce((phi, psi) => app(Fun.and, phi, psi))
      val lines = Printer.lines(app(Fun.imp, p, app(Fun.and, app(Fun.imp, app(Fun.int.lt, x, y), long), q)))
      val open = lines.find(_.contains("(x < y")).get.indexOf("(")
      val inner = lines.dropWhile(!_.contains("(x < y")).tail.takeWhile(!_.contains("q"))
      assert(inner.nonEmpty && inner.forall(_.indexWhere(_ != ' ') > open))

    // conjunctions of comparisons that are linked by their operands in one direction are chained,
    // comparisons as operands of comparisons are parenthesized
    test("chained comparisons"):
      expr(app(Fun.and, app(Fun.int.le, zero, x), app(Fun.int.lt, x, y))) ==> "0 <= x < y"
      expr(app(Fun.and, app(Fun.and, app(Fun.int.le, zero, x), app(Fun.int.lt, x, y)), p)) ==> "0 <= x < y && p"
      expr(app(Fun.and, app(Fun.int.lt, zero, x), app(Fun.int.lt, y, x))) ==> "0 < x && y < x"
      expr(app(Fun.and, app(Fun.int.lt, zero, x), app(Fun.int.gt, x, y))) ==> "0 < x && x > y"
      expr(app(Fun.eq_, app(Fun.eq_, x, y), p)) ==> "(x == y) == p"

    test("mixfix prefix"):
      expr(app(Fun.not, app(Fun.and, p, q))) ==> "!(p && q)"
      expr(app(Fun.and, app(Fun.not, p), q)) ==> "!p && q"
      expr(app(Fun.eq_, app(Fun.not, p), q)) ==> "!p == q"
      expr(app(Fun.int.uminus, app(Fun.int.uminus, x))) ==> "-(-x)"
      expr(app(Fun.int.plus, app(Fun.int.uminus, x), y)) ==> "-x + y"

    test("mixfix binders"):
      val all = Bind("forall", List(x), app(Fun.int.lt, x, y))
      expr(app(Fun.and, all, p)) ==> "(forall x: int :: x < y) && p"

    // combinators that do not fit have the keyword below for and the update below the keyword
    test("combinator breaks"):
      val sequence = Var("a_rather_long_sequence_of_values", Sort.seq(Sort.int))
      val other = Var("another_rather_long_sequence", Sort.seq(Sort.int))
      val (u, v) = (Var("u", Sort.int), Var("v", Sort.int))
      val all = Invs(List(sequence, other), List(u, v), Lt.int(u, v))
      Printer.lines(all) ==> List(
        "all(for a_rather_long_sequence_of_values, another_rather_long_sequence",
        "    check u, v =>",
        "      u < v)"
      )

    // the arguments flow up to the width, aligned after the opening parenthesis
    test("long call breaks"):
      val args = List.fill(12)(Var("argument", Sort.int))
      val lines = Printer.lines(Call("procedure", args, List(x))).filter(_.nonEmpty)
      lines.head ==> "x := procedure(argument, argument, argument, argument, argument, argument,"
      lines.last ==> "               argument, argument, argument, argument, argument, argument);"
      assert(lines.forall(_.length <= Printer.width))
