package cuvee.test
package smtlib

import utest._

import cuvee.Error
import cuvee.core._
import cuvee.core.Attrs
import cuvee.sexpr.Id
import cuvee.sexpr.Str

// checks commands directly against the solver sink, where the answers depend on the solver or the state of the sink
// is inspected (see examples/smtlib/solver for scripts with their answers)
object Solver extends TestSuite:
  def const(name: String, typ: Type) =
    Fun(name, Nil, Nil, typ)

  def declare(fun: Fun) =
    DeclareFun(fun, Attrs.empty)

  def axiom(phi: Expr) =
    Assert(Axiom, Nil, phi, Attrs.empty)

  val models = SetOption("produce-models", Id("true"))

  val x = const("x", Sort.int)

  // runs `cmds` on a fresh solver and returns the result of the last one,
  // the solver is stopped even if a check fails
  def run(solver: cuvee.smtlib.Solver)(cmds: Cmd*): Result =
    try
      val (init, _, _) = cuvee.smtlib.Source.newParser(cuvee.Config.default)
      val sink = cuvee.smtlib.Solver.sink(solver, init)
      val (result, _, _) = sink.exec(cmds.init.toList).query(cmds.last)
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
        val (ack, _, _) = sink.query(DefineFun(f, y, attrs))

        ack ==> Ack.Success
        sink.parser.state.funattrs(("f", 1)) ==> attrs
      finally solver.destroy()

    // the scope of a solver that has terminated is not popped, which would fail with an unrelated error
    test("scopes of terminated solvers"):
      val solver = cuvee.smtlib.Solver.z3()
      val error =
        try
          solver.scoped:
            solver.destroy()
            solver.proc.waitFor()
          None
        catch case e: Error => Some(e.msg)

      error ==> Some("solver terminated unexpectedly")
