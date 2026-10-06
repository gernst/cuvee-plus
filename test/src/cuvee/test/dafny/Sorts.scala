package cuvee.test
package dafny

import utest._

import cuvee.core._

// defined sorts are expanded in expressions and programs by type checking, also in the types of variables,
// but not in the declarations, whose formal parameters keep them
object DefinedSorts extends TestSuite:
  val program =
    """type T = int
      |var count: T
      |
      |method incr(y: T) returns (z: T)
      |  modifies count
      |  ensures z == y + 1 && count == old(count) + 1
      |{
      |  z := y + 1;
      |  count := count + 1;
      |}
      |
      |method twice(a: T) returns (b: T)
      |  modifies count
      |  ensures b == a + 2 && count == old(count) + 2
      |{
      |  var c: T;
      |  c := a;
      |  b := incr(c);
      |  b := incr(b);
      |}
      |
      |lemma forall x: T :: x + 1 - 1 == x
      |""".stripMargin

  val T = Sort(Con("T", 0), Nil)

  // the types in an expression, including those of variables and of applications
  def types(expr: Expr): List[Type] =
    val inner = List.newBuilder[Type]
    expr.map: arg =>
      inner ++= types(arg)
      arg
    val own =
      expr match
        case x: Var                    => List(x.typ)
        case App(_, inst, typ, _)      => typ :: inst
        case Bind(_, bound, _)         => bound.types
        case _                         => Nil
    own ++ inner.result()

  def types(prog: Prog): List[Type] =
    val own =
      prog match
        case Assign(lhs, rhs)       => lhs.types ++ rhs.flatMap(types)
        case Call(_, args, res)     => res.types ++ args.flatMap(types)
        case Block(locals, progs)   => locals.types
        case _                      => Nil
    own ++ prog.subprogs.flatMap(types)

  val tests = Tests:
    test("expanded"):
      val file = os.temp(program, suffix = ".dfy")
      val (cmds, errors) = Examples.output("-print", "null", file.toString)
      errors ==> Nil

      val List(incr, twice) = cmds.collect { case DefineProc(proc, body, attrs) => (proc, body, attrs) }: @unchecked
      val List(lemma) = cmds.collect { case Assert(Lemma, _, phi, _) => phi }: @unchecked

      // the formal parameters keep the defined sort
      incr._1.in.types ==> List(T)
      twice._1.out.types ==> List(T)

      for (_, body, attrs) <- List(incr, twice)
      do
        assert(!types(body).contains(T))
        assert(!types(attrs.ensures).contains(T))
        assert(!types(attrs.ensures).isEmpty)

      assert(!types(lemma).contains(T))

    // the verification conditions quantify over the formal parameters and global variables with their types expanded,
    // such that they bind the variables of the body
    test("verify"):
      Examples.check("dfy", program, "-verify", "-z3") ==> Nil

    // arithmetic on defined sorts is normalized, which was a type mismatch before
    test("simplify"):
      val file = os.temp(program, suffix = ".dfy")
      val (cmds, errors) = Examples.output("-simplify", "-print", "null", file.toString)
      errors ==> Nil
      cmds.collect { case cmd @ Assert(Lemma, _, _, _) => cmd } ==> Nil

    // the predicates of the procedures have the expanded types of the formal parameters and global variables
    test("horn"):
      val text =
        """type T = int
          |var count: T
          |
          |method incr(y: T) returns (z: T)
          |  modifies count
          |{
          |  z := y + 1;
          |  count := count + 1;
          |}
          |
          |method main(a: T) returns (b: T)
          |  modifies count
          |{
          |  var c: T;
          |  c := count;
          |  b := incr(a);
          |  assert b == a + 1 && count == c + 1;
          |}
          |""".stripMargin
      val file = os.temp(text, suffix = ".dfy")
      val (_, results) = cuvee.Cuvee.run("-chc", "-z3", file.toString)
      Examples.status(results) ==> Status.Sat
