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
    Examples.source(cuvee.c.Source, new java.io.StringReader(text))._2.toList

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

    // only the branch of ?: that is taken makes its calls and updates
    test("calls in conditional expressions"):
      val f = "int c; int f(void) { c = c + 1; return 1; } "
      horn(f + "int main(void) { int i = 0; int r = 1 ? f() : i++; assert(c == 1 && i == 0 && r == 1); r = 0 ? f() : i++; assert(c == 1 && i == 1 && r == 0); return 0; }") ==> Status.Sat
      horn(f + "int main(void) { int r = 0 ? f() : 2; assert(c == 1); return 0; }") ==> Status.Unsat

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

    // the names of types are replaced by their definitions, which fail only where they are used
    test("typedefs"):
      valid("typedef unsigned int size_t; typedef size_t index; __extension__ typedef long long int big; " +
        "int main(void) { index i = 3; big b = (big) i * 2; assert(b == 6); return 0; }")
      errors("typedef struct { int n; } S; int main(void) { return 0; }") ==> Nil
      errors("typedef struct { int n; } S; int main(void) { S s; return 0; }") ==> List("parse error")

    // the sizes of integer types are those of the data models ILP32 (-arch 32) and LP64 (-arch 64, the default), which differ for long
    test("sizeof"):
      valid("typedef unsigned int size_t; int main(void) { assert(sizeof(int) == 4 && sizeof(unsigned long long) == 8 && sizeof(char) == 1 && sizeof(short int) == 2 && sizeof(size_t) == 4); return 0; }")
      valid("int main(void) { assert(sizeof(long) == 8 && sizeof(long int) == 8); return 0; }")
      Examples.check("c", "int main(void) { assert(sizeof(long) == 4); return 0; }", "-arch", "32", "-verify", "-z3") ==> Nil
      errors("int main(void) { int a[2]; return sizeof(a); }") ==> List("sizeof of an expression is not supported")

    // memory for n elements is an array, whose elements are arbitrary, or zero for calloc
    test("allocations"):
      valid("void *malloc(unsigned int size); void *calloc(unsigned int n, unsigned int size); void free(void *p); " +
        "int main(void) { int n = 3; int *a = malloc(sizeof(int) * n); a[1] = 2; assert(a[1] == 2); free(a); " +
        "long *b = (long *) malloc(n * sizeof(long)); b[0] = 1; int *c = calloc(n, sizeof(int)); assert(c[2] == 0); return 0; }")
      Examples.check("c", "void *malloc(unsigned int size); int main(void) { int *a = malloc(sizeof(int) * 2); assert(a[0] == 0); return 0; }", "-verify", "-z3") ==>
        List("goal does not hold")
      errors("int main(void) { int *p = 0; return 0; }") ==> List("pointers are not supported")
      errors("int *g; int main(void) { return 0; }") ==> List("pointers are not supported")

    // nondeterministic values of unsigned types are nonnegative, those of signed types are not
    test("unsigned nondeterministic values"):
      valid("int main(void) { unsigned int x = __VERIFIER_nondet_uint(); assert(x >= 0); x = __VERIFIER_nondet_ulong(); " +
        "assert(x >= 0); int y = __VERIFIER_nondet_size_t() + 1; assert(y > 0); return 0; }")
      Examples.check("c", "int main(void) { int x = __VERIFIER_nondet_int(); assert(x >= 0); return 0; }", "-verify", "-z3") ==>
        List("goal does not hold")

    // the value of x++ is the old one, that of ++x the new one, the update is made before the expression
    test("increments in expressions"):
      valid("int main(void) { int i = 0; int a[3]; a[i++] = 5; assert(i == 1 && a[0] == 5); int j = ++i; assert(j == 2 && i == 2); " +
        "int k = i--; assert(k == 2 && i == 1); assert(--i == 0); return 0; }")
      horn("int main(void) { int counter = 0; int x = 0; while (counter++ < 10) x++; assert(x == 10 && counter == 11); return 0; }") ==> Status.Sat
      errors("int f(int n) { while (n-- > 0) ; return n; }") ==> Nil
      modifies(parse("int g; int f(void) { return g++; }"), "f") ==> Some(List("g"))

    // the comma operator in expression statements and in for loops
    test("comma"):
      valid("int main(void) { int i; int j; i = 0, j = 1; assert(i == 0 && j == 1); return 0; }")
      horn("int main(void) { int i; int j; for (i = 0, j = 4; i < j; i++, j--) ; assert(i == j); return 0; }") ==> Status.Sat

    test("unexpected character"):
      errors("int f(int x) { return x @ 1; }") ==> List("unexpected character '@' at 0:24")

    test("__VERIFIER_assert"):
      Examples.check("c", "void __VERIFIER_assert(int c); int main(void) { __VERIFIER_assert(0); return 0; }", "-verify", "-z3") ==>
        List("goal does not hold")

// the output is C: what is not C is omitted, e.g. contracts, assertions, and quantifiers
object Printing extends TestSuite:
  val x = Var("x", Sort.int)
  val g = Var("g", Sort.int)
  val p = Fun("p", Nil, Fun.formals(Sort.int), Sort.bool)

  def print(cmd: Cmd) =
    cuvee.c.Printer.lines(cmd)

  val tests = Tests:
    test("assertions"):
      print(Assert(Axiom, Nil, All(List(x), Imp(App(p, List(x)), Lt.int(x, One.int))), Attrs.empty)) ==> Nil

    test("declarations"):
      print(DeclareFun(p, Attrs.empty)) ==> List("_Bool p(int x_0);", "")
      print(DefineFun(p, Ex(List(x), Lt.int(x, One.int)), Attrs.empty)) ==> Nil
      print(CheckSat) ==> Nil

    // models are not programs, they are SMT-LIB
    test("models"):
      val model = Model(List(DefineFun(p, Lt.int(Var("x", Sort.int), One.int), Attrs.empty)))
      cuvee.c.Printer.lines(model) ==> cuvee.smtlib.Printer.lines(model)

    // names of the input that end like those of temporaries are kept apart from them
    test("names"):
      val file = os.temp("int f(void); int main(void) { int tmp_1 = 2; int r = tmp_1 + f(); return r; }", suffix = ".c")
      val out = os.temp(suffix = ".c")
      Examples.errors(file.toString, "-o", out.toString) ==> Nil
      val text = os.read(out)
      assert(text.contains("tmp_1_ = 2"))
      assert(text.contains("tmp_1 = f()"))

    // nondeterministic values of unsigned types are nonnegative, which is assumed after the value
    test("unsigned nondeterministic values"):
      val file = os.temp("int main(void) { unsigned int x = __VERIFIER_nondet_uint(); return x; }", suffix = ".c")
      val out = os.temp(suffix = ".c")
      Examples.errors(file.toString, "-o", out.toString) ==> Nil
      val text = os.read(out)
      assert(text.contains("tmp_1 = __VERIFIER_nondet_int();\n  __VERIFIER_assume(0 <= tmp_1);"))

    // global variables are zero in C, initializers are assignments at the beginning of main
    test("contracts"):
      val file = os.temp("int g = 1; int main(void) { return g; }", suffix = ".c")
      val out = os.temp(suffix = ".c")
      Examples.errors(file.toString, "-o", out.toString) ==> Nil
      os.read(out) ==> "int g;\n\nint main(void) {\n  g = 1;\n  return g;\n}\n\n"
