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
      Printer.lines(Spec.assume(Lt.int(x, y))) ==> List("assume x < y;")
      Printer.lines(Spec.havoc(List(x, y))) ==> List("havoc x, y;")
      Printer.lines(Spec(List(x), Lt.int(zero, x), Lt.int(x, y))) ==>
        List("spec x requires 0 < x ensures x < y;")

    test("choice"):
      val progs = List(Assign(List(x), List(zero)), Assign(List(x), List(y)))
      Printer.lines(Choice(progs)) ==> List("if * {", "  x := 0;", "} else {", "  x := y;", "}")

    test("else if"):
      val prog = If(Lt.int(x, y), Break, If(Lt.int(y, x), Continue, Block(Nil, Nil)))
      Printer.lines(prog) ==> List("if x < y {", "  break;", "} else if y < x {", "  continue;", "}")

    test("iter"):
      val attrs = cuvee.core.Attrs(List("invariant" -> Some(Le.int(x, y))))
      Printer.lines(Iter(Assign(List(x), List(y)), attrs)) ==>
        List("while *", "  invariant x <= y", "{", "  x := y;", "}")

    // the evolution constraint follows while, the right hand sides need no parentheses
    test("ode"):
      val dom = Le.int(zero, x)
      val inv = cuvee.core.Attrs(List("invariant" -> Some(Le.int(x, y))))
      val t = Var("t", Sort.real)
      Printer.lines(Ode(t, List(x, y), List(y, UMinus.int(x)), True, cuvee.core.Attrs.empty)) ==>
        List("ode t :: x', y' == y, -x;")
      Printer.lines(Ode(t, List(p), List(And(p, q)), dom, inv)) ==>
        List("ode t :: p' == p && q while 0 <= x", "  invariant x <= y;")

    test("diff"):
      expr(Diff(List(x), x)) ==> "(x :: x)'"
      expr(Diff(List(x, y), Times.int(x, y))) ==> "(x, y :: x * y)'"
      expr(UMinus.int(Diff(List(x), x))) ==> "-(x :: x)'"

    // real literals have a decimal point, fractions without finite decimal expansion are divisions
    test("real literals"):
      val real = (r: _root_.util.Rational) => Lit(r, Sort.real)
      val x = Var("x", Sort.real)
      expr(real(_root_.util.Rational(2))) ==> "2.0"
      expr(real(_root_.util.Rational(-3, 2))) ==> "-1.5"
      expr(real(_root_.util.Rational(1, 3))) ==> "1.0 / 3.0"
      expr(real(_root_.util.Rational(-1, 3))) ==> "-1.0 / 3.0"
      expr(Times.real(real(_root_.util.Rational(1, 3)), x)) ==> "1.0 / 3.0 * x"
      expr(Times.real(x, real(_root_.util.Rational(1, 3)))) ==> "x * (1.0 / 3.0)"

    // sequence literals are concatenations of units, + and <= are overloaded, x in s is containment of [x]
    test("sequences"):
      val s = Var("s", Sort.seq(Sort.int))
      val one = Lit(BigInt(1), Sort.int)
      val unit = (e: Expr) => Seqs.unit(e)
      expr(Seqs.empty(Sort.int)) ==> "[]"
      expr(Seqs.concat(unit(x), unit(y))) ==> "[x, y]"
      expr(Seqs.concat(s, unit(x))) ==> "s + [x]"
      expr(Seqs.prefixof(unit(x), s)) ==> "[x] <= s"
      expr(Seqs.contains(s, unit(x))) ==> "x in s"
      expr(Seqs.len(s)) ==> "|s|"
      expr(Seqs.nth(s, zero)) ==> "s[0]"
      expr(Seqs.update(s, zero, unit(x))) ==> "s[0 := x]"
      expr(Seqs.extract(s, one, Minus.int(x, one))) ==> "s[1..x]"
      expr(Seqs.extract(s, zero, x)) ==> "s[0..x]"

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
      expr(Plus.int(As(x, Sort.int), y)) ==> "x as int + y"
      expr(Seqs.nth(As(s, Seq), zero)) ==> "(s as seq<int>)[0]"

    test("mixfix"):
      expr(Plus.int(Plus.int(x, y), zero)) ==> "x + y + 0"
      expr(Plus.int(x, Plus.int(y, zero))) ==> "x + (y + 0)"
      expr(app(Fun.int.plus, x, y, zero)) ==> "x + y + 0"
      expr(Times.int(Plus.int(x, y), Minus.int(x, y))) ==> "(x + y) * (x - y)"
      expr(Minus.int(x, Times.int(y, Lit(BigInt(-1), Sort.int)))) ==> "x - y * -1"
      expr(Imp(p, Imp(q, p))) ==> "p ==> q ==> p"
      expr(Imp(Imp(p, q), p)) ==> "(p ==> q) ==> p"
      expr(And(Or(p, q), Lt.int(x, y))) ==> "(p || q) && x < y"

    test("mixfix non-associative"):
      expr(Eq(Lt.int(x, y), p)) ==> "(x < y) == p"
      expr(Eq(p, Eq(q, p))) ==> "p == (q == p)"
      expr(app(Fun.eq_, x, y, zero)) ==> "==(x, y, 0)"

    // conjunctions of comparisons that are linked by their operands in one direction are chained,
    // comparisons as operands of comparisons are parenthesized
    test("chained comparisons"):
      expr(And(Le.int(zero, x), Lt.int(x, y))) ==> "0 <= x < y"
      expr(And(And(Le.int(zero, x), Lt.int(x, y)), p)) ==> "0 <= x < y && p"
      expr(And(Lt.int(zero, x), Lt.int(y, x))) ==> "0 < x && y < x"
      expr(And(Lt.int(zero, x), Gt.int(x, y))) ==> "0 < x && x > y"
      expr(Eq(Eq(x, y), p)) ==> "(x == y) == p"

    test("mixfix prefix"):
      expr(Not(And(p, q))) ==> "!(p && q)"
      expr(And(Not(p), q)) ==> "!p && q"
      expr(Eq(Not(p), q)) ==> "!p == q"
      expr(UMinus.int(UMinus.int(x))) ==> "-(-x)"
      expr(Plus.int(UMinus.int(x), y)) ==> "-x + y"

    test("mixfix binders"):
      val all = Bind("forall", List(x), Lt.int(x, y))
      expr(And(all, p)) ==> "(forall x: int :: x < y) && p"

    // -linewidth sets the width of all printers, which are objects, hence reset afterwards
    test("linewidth"):
      try
        cuvee.Config.parse(cuvee.Config.default, List("-linewidth", "40"))
        Printer.width ==> 40
        cuvee.smtlib.Printer.width ==> 40
        cuvee.sexpr.Printer.width ==> 40
        val long = (1 to 8).map(i => Lt.int(x, Lit(BigInt(1000 * i), Sort.int))).reduce(And(_, _))
        assert(Printer.lines(long).forall(_.length <= 40))
        assert(Printer.lines(long).length > 1)
      finally
        for lang <- cuvee.Config.langs.values
        do lang.printer.width = 160
        cuvee.sexpr.Printer.width = 160

    // names that are neither identifiers nor operators are escaped by backticks, which the scanner reads back,
    // e.g. the instances of Monomorph
    test("escaped names"):
      val f = Fun("f<pair<Int>>", Nil, Fun.formals(Sort.int), Sort.int)
      expr(App(f, List(x))) ==> "`f<pair<Int>>`(x)"
      expr(Lt.int(x, y)) ==> "x < y"

      val text = "function `f<Int>`(x: int): int\nlemma forall x: int :: `f<Int>`(x) == x\n"
      val (cmds, errors) = Examples.output("-print", "null", os.temp(text, suffix = ".dfy").toString)
      errors ==> Nil
      cmds.collect { case DeclareFun(fun, _) => fun.name.name } ==> List("f<Int>")

