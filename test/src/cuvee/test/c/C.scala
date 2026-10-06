package cuvee.test
package c

import utest._

import cuvee.core._

// the C examples parse and print back to the same program, including division and remainder
object Parsing extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c")): file =>
      Examples.errors("-print", "null", file.toString) ==> Nil

object Roundtrip extends TestSuite:
  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c")): file =>
      val first = os.temp(suffix = ".c")
      val second = os.temp(suffix = ".c")

      Examples.errors(file.toString, "-o", first.toString) ==> Nil
      Examples.errors(first.toString, "-o", second.toString) ==> Nil
      val third = os.temp(suffix = ".c")
      Examples.errors(second.toString, "-o", third.toString) ==> Nil
      os.read(third) ==> os.read(second)

// the examples without loops are verified with -verify, since C has no loop invariants,
// and all examples with -chc, except for division by variables, for which z3 answers unknown;
// the first line of each example states whether all assertions hold
object Verify extends TestSuite:
  def loops(file: os.Path) =
    List("while", "for", "do").exists(os.read(file).contains)

  def expected(file: os.Path) =
    os.read.lines(file).head match
      case "// expected: valid"   => true
      case "// expected: invalid" => false

  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c").filterNot(loops)): file =>
      val errors = Examples.errors("-verify", "-z3", file.toString)
      errors ==> (if expected(file) then Nil else List("goal does not hold"))

object Horn extends TestSuite:
  val skip = Set("div.c")

  val tests =
    Examples.tests(Examples.find(os.sub / "c", "c").filterNot(file => skip.contains(file.last))): file =>
      val (_, results) = cuvee.Cuvee.run("-chc", "-z3", file.toString)
      Examples.status(results) ==> (if Verify.expected(file) then Status.Sat else Status.Unsat)

// the translation of C: conversions between integers and truth values, the inferred modifies attributes,
// and the constructs that are rejected
object Translation extends TestSuite:
  def parse(text: String) =
    cuvee.c.Source(new java.io.StringReader(text))._2.toList

  def errors(text: String) =
    Examples.check("c", text)

  def modifies(cmds: List[Cmd], name: String) =
    cmds.collectFirst:
      case DefineProc(Proc(_root_.util.Name(`name`, None), _, _, _), _, attrs) => attrs.modifies.map(_.name.name)

  val tests = Tests:
    test("modifies"):
      val cmds = parse("int g; int h; void f(void) { g = 1; } void k(void) { int h; h = 2; f(); } void m(void) { k(); }")
      modifies(cmds, "f") ==> Some(List("g"))
      modifies(cmds, "k") ==> Some(List("g"))
      modifies(cmds, "m") ==> Some(List("g"))

    test("conditions"):
      errors("int f(int x) { if (x) return !x; else return x && 1; }") ==> Nil

    // the status of the Horn clauses of a program, sat if its assertions hold
    def horn(text: String) =
      val file = os.temp(text, suffix = ".c")
      val (_, results) = cuvee.Cuvee.run("-chc", "-z3", file.toString)
      Examples.status(results)

    // the right operand is evaluated only if the left one does not determine the result
    test("calls in conditions"):
      val f = "int c; int f(void) { c = c + 1; return 1; } "
      horn(f + "int main(void) { int r; r = 0 && f(); assert(c == 0); r = 1 || f(); assert(c == 0); r = 1 && f(); assert(c == 1 && r); return 0; }") ==> Status.Sat
      horn(f + "int main(void) { int r; r = 0 || f(); assert(c == 0); return 0; }") ==> Status.Unsat

    // calls in the conditions of loops are evaluated before each iteration, also after continue
    test("calls in loop conditions"):
      val nondet = "extern _Bool __VERIFIER_nondet_bool(void); "
      horn(nondet + "int main(void) { int i = 0; while (__VERIFIER_nondet_bool()) i++; assert(i >= 0); return 0; }") ==> Status.Sat
      horn(nondet + "int main(void) { int i = 0; while (__VERIFIER_nondet_bool()) i++; assert(i == 0); return 0; }") ==> Status.Unsat
      horn(nondet + "int main(void) { int i = 0; do i++; while (__VERIFIER_nondet_bool()); assert(i >= 1); return 0; }") ==> Status.Sat
      horn(nondet + "int main(void) { int i = 0; do i++; while (__VERIFIER_nondet_bool()); assert(i == 1); return 0; }") ==> Status.Unsat
      horn(nondet + "int main(void) { int i; int j = 0; for (i = 0; __VERIFIER_nondet_bool(); i++) { if (i > 2) continue; j++; } assert(j <= 3 && j <= i); return 0; }") ==> Status.Sat

    // the initial values are the precondition of main, they must not call functions
    test("initialized globals"):
      errors("int g = 1; int main(void) { return g; }") ==> Nil
      errors("int f(void); int g = f();") ==> List("initial value of global variable must not call functions")
      errors("int a[2] = 1;") ==> List("initialized global array")

    test("unknown variable"):
      errors("int f(void) { return y; }") ==> List("unknown variable")

    // the harness of SV-COMP (see examples/c/harness.c): pointers only in the signatures of builtins
    test("pointers"):
      errors("extern void __assert_fail(const char *, const char *, unsigned int, const char *);") ==> Nil
      errors("int f(int *p);") ==> List("pointers are not supported")
      errors("extern double __VERIFIER_nondet_double(void);") ==> Nil
      errors("double f(void);") ==> List("floating point numbers are not supported")

    test("unnamed parameters"):
      errors("int f(int, int); int main(void) { return f(1, 2); }") ==> Nil

    test("labels"):
      val cmds = parse("int g; void f(void) { L: g = 1; }")
      modifies(cmds, "f") ==> Some(List("g"))

    test("literals"):
      val text =
        "int main(void) { assert(0x1F == 31); assert(010 == 8); assert(7UL == 7); assert(0xffffffffu == 4294967295LL); " +
          "assert('a' == 97); assert('\\n' == 10); assert('\\0' == 0); assert('\\x41' == 65); assert('\\'' == 39); return 0; }"
      Examples.check("c", text, "-verify", "-z3") ==> Nil

    def valid(text: String) =
      Examples.check("c", text, "-verify", "-z3") ==> Nil

    // casts to integer types are the identity, to _Bool a comparison with zero
    test("casts"):
      valid("int main(void) { long long y = (long long) 2 * 3; assert(y == 6); assert((int) -1 == -1); assert((_Bool) 5 == 1); return 0; }")
      errors("int main(void) { return (void) 0; }") ==> List("unsupported cast")

    test("multidimensional arrays"):
      valid("int main(void) { int a[2][3]; a[1][2] = 5; a[1][2] += 1; assert(a[1][2] == 6); return 0; }")
      modifies(parse("int g[2][2]; void f(void) { g[0][1] = 1; }"), "f") ==> Some(List("g"))

    // the elements that are not given are zero
    test("initializer lists"):
      valid("int g[3] = {1, 2}; int main(void) { int a[2][2] = {{1, 2}, {3}}; assert(a[1][0] == 3 && a[1][1] == 0 && g[1] == 2 && g[2] == 0); return 0; }")
      errors("int main(void) { int x = {1}; return x; }") ==> List("initializer list outside of a declaration")

    test("chained assignments"):
      valid("int main(void) { int i; int k; i = k = 2; assert(i == 2 && k == 2); return 0; }")

    test("unexpected character"):
      errors("int f(int x) { return x @ 1; }") ==> List("unexpected character '@' at 0:24")

    test("__VERIFIER_assert"):
      Examples.check("c", "void __VERIFIER_assert(int c); int main(void) { __VERIFIER_assert(0); return 0; }", "-verify", "-z3") ==>
        List("goal does not hold")

// formulas that are not C are written in a notation after ACSL
object Annotations extends TestSuite:
  val x = Var("x", Sort.int)
  val p = Fun("p", Nil, Fun.formals(Sort.int), Sort.bool)

  val tests = Tests:
    test("quantifiers"):
      val phi = All(List(x), Imp(App(p, List(x)), Lt.int(x, One.int)))
      cuvee.c.Printer.lines(Assert(Axiom, Nil, phi, Attrs.empty)) ==> List("/*@ axiom \\forall int x; p(x) ==> x < 1; */", "")

    test("declarations"):
      cuvee.c.Printer.lines(DeclareFun(p, Attrs.empty)) ==> List("_Bool p(int x_0);", "")
