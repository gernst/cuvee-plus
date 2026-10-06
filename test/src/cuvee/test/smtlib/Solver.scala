package cuvee.test
package smtlib

import utest._

import cuvee.Error
import cuvee.core._
import cuvee.core.Attrs
import cuvee.sexpr.Id
import cuvee.sexpr.Str

// checks commands and queries directly against the solver sink
object Solver extends TestSuite:
  def const(name: String, typ: Type) =
    Fun(name, Nil, Nil, typ)

  def declare(fun: Fun) =
    DeclareFun(fun, Attrs.empty)

  def axiom(phi: Expr) =
    Assert(Axiom, Nil, phi, Attrs.empty)

  val models = SetOption("produce-models", Id("true"))

  val x = const("x", Sort.int)
  val x_ = App(x, Nil)

  // runs `cmds` on a fresh solver and returns the result of the last one,
  // the solver is stopped even if a check fails
  def run(solver: cuvee.smtlib.Solver)(cmds: Cmd*): Result =
    try
      val (init, _, _) = cuvee.smtlib.Source.newParser(cuvee.Config.default)
      val sink = cuvee.smtlib.Solver.sink(solver, init)
      val (result, _) = sink.exec(cmds.init.toList).query(cmds.last)
      result
    finally solver.destroy()

  def z3(cmds: Cmd*) =
    run(cuvee.smtlib.Solver.z3())(declare(x) +: cmds*)

  // names of the functions defined by a model
  def defined(result: Result) =
    result match
      case Model(decls) =>
        decls.collect { case DefineFun(fun, _, _) => fun.name.name }.toSet

      case _ =>
        Set()

  val tests = Tests:
    test("valid lemma"):
      z3(Assert(Lemma, Nil, Eq(x_, x_), Attrs.empty))

    test("invalid lemma"):
      val error = assertThrows[Error]:
        z3(Assert(Lemma, Nil, Eq(x_, Zero.int), Attrs.empty))
      error.msg ==> "lemma does not hold"

    // free lemmas are assumed like axioms, without proof
    test("free lemma"):
      z3(
        Assert(Lemma, Nil, Eq(x_, One.int), Attrs(List("free" -> None))),
        Assert(Goal, Nil, Lt.int(Zero.int, x_), Attrs.empty)
      )

    test("invalid goal"):
      val error = assertThrows[Error]:
        z3(Assert(Goal, Nil, Eq(x_, Zero.int), Attrs.empty))
      error.msg ==> "goal does not hold"

    test("goal from axiom"):
      z3(
        axiom(Eq(x_, One.int)),
        Assert(Lemma, Nil, Lt.int(Zero.int, x_), Attrs.empty),
        Assert(Goal, Nil, Lt.int(Zero.int, x_), Attrs.empty)
      )

    // the state of the sink must follow the scopes of the solver
    test("declarations are scoped"):
      val y = declare(const("y", Sort.int))
      z3(Push(1), y, Pop(1), y)

    test("pop below the stack"):
      val error = assertThrows[Error]:
        z3(Push(1), Pop(2))
      error.msg ==> "cannot pop 2 levels from stack of size 1"

    test("get-info"):
      z3(GetInfo("name")) ==> Info(Attrs(List("name" -> Some(Str("Z3")))))

    test("unsupported get-info"):
      z3(GetInfo("foo")) ==> Ack.Unsupported

    test("get-option"):
      z3(models, GetOption("produce-models")) ==> Value(Id("true"))

    // labels are only available after check-sat
    test("labels"):
      z3(CheckSat, Labels) ==> Labels(Nil)

    test("model"):
      z3(models, axiom(Eq(x_, One.int)), CheckSat, GetModel) ==>
        Model(List(DefineFun(x, One.int, Attrs.empty)))

    // z3 declares the elements of uninterpreted sorts with a cardinality constraint,
    // and writes constant arrays with (as const ...)
    test("model with sorts and arrays from z3"):
      val U = Sort(Con("U", 0), Nil)
      val u = const("u", U)
      val v = const("v", U)
      val a = const("a", Sort.array(Sort.int, Sort.bool))

      val model = z3(
        models,
        DeclareSort(Con("U", 0), Attrs.empty),
        declare(u),
        declare(v),
        declare(a),
        axiom(Not(Eq(App(u, Nil), App(v, Nil)))),
        axiom(Select(App(a, Nil), Lit(BigInt(2), Sort.int))),
        CheckSat,
        GetModel
      )

      defined(model) ==> Set("x", "u", "v", "a")

    // cvc5 writes elements of uninterpreted sorts as abstract values (as @U_0 U)
    test("model with sorts from cvc5"):
      val U = Sort(Con("U", 0), Nil)
      val u = const("u", U)
      val v = const("v", U)

      val model = run(cuvee.smtlib.Solver.cvc5())(
        models,
        SetLogic("ALL"),
        DeclareSort(Con("U", 0), Attrs.empty),
        declare(u),
        declare(v),
        axiom(Not(Eq(App(u, Nil), App(v, Nil)))),
        CheckSat,
        GetModel
      )

      defined(model) ==> Set("u", "v")

    // SMT-LIB does not admit attributes on definitions, they are only kept in the state of the sink
    test("attributes are not sent to the solver"):
      val y = Var("y", Sort.int)
      val f = Fun("f", Nil, List(y), Sort.int)
      val attrs = Attrs(List("requires" -> Some(Lt.int(Zero.int, y))))

      val solver = cuvee.smtlib.Solver.z3()
      try
        val (init, _, _) = cuvee.smtlib.Source.newParser(cuvee.Config.default)
        val sink = cuvee.smtlib.Solver.sink(solver, init)
        val (ack, _) = sink.query(DefineFun(f, y, attrs))

        ack ==> Ack.Success
        sink.parser.state.funattrs(("f", 1)) ==> attrs
      finally solver.destroy()
