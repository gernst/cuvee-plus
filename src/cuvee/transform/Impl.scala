package cuvee.transform

import util.Name
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.sexpr.Id
import cuvee.sexpr.Str

// implementations of the functions of the core, e.g. those of sets, sequences, and maps, by procedures whose contracts
// may leave the result open, i.e., nondeterministic operations: a procedure with the attribute :implements f
// implements the function named f of the same arity by its single output; the applications of such functions in the
// expressions that programs execute become calls, in the order of evaluation, whose results are fresh locals, such that
// each evaluation chooses anew; the right-hand sides of && || ==> and ite are evaluated only if they are needed, as are
// their calls, which become conditionals, and the calls of a loop guard are made before each test, the loop becomes an
// iteration that breaks if the guard is false, whose invariants hold at the beginning of each iteration, before these
// calls; specifications keep the functions: contracts, invariants, assertions, assumptions, the bodies of functions,
// and the implementing procedures, which must not rely on implementations themselves; applications under binders,
// which bind variables of the arguments, and under old, which evaluates them in another state, are not supported
object Impl extends Transform:
  // the entry of the implementations, injected before the modules of -include impl:<name> (see Config.features),
  // with the source that parses it
  val modules =
    List((cuvee.dafny.Source, "/cuvee/impl.dfy"))

  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Option[Cmd]): (List[Cmd], Option[Cmd]) =
    val procs = implementations(state)

    val cmds_ =
      for cmd <- cmds
      yield cmd match
        case DefineProc(proc, body, attrs) if procs.nonEmpty && !attrs.contains("implements") =>
          DefineProc(proc, impl(state, procs, body), attrs)

        case _ =>
          cmd

    (cmds_, last)

  // the implementing procedures by the name and arity of the function they implement, where the name is that of the
  // core, e.g. set.member, written as a string or symbol
  def implementations(state: State): Map[(Name, Int), Proc] =
    val entries =
      for
        (name, attrs) <- state.procattrs.toList
        value <- attrs.get("implements")
      yield
        val proc = state.procs(name)
        val fun = value match
          case Some(fun: String) => Name(fun, None)
          case Some(Str(fun))    => Name(fun, None)
          case Some(Id(fun))     => Name(fun, None)
          case Some(fun: Name)   => fun
          case _                 => Error.raise("the implemented function must be named", name, value)

        Error.report("an implementing procedure has a single output", name, proc.out):
          require(proc.out.length == 1)

        (fun, proc.in.length) -> proc

    Error.report("functions with several implementations", entries.map(_._1).diff(entries.map(_._1).distinct)):
      require(entries.map(_._1).distinct.length == entries.length)

    entries.toMap

  // whether `expr` applies an implemented function, needed only where its applications cannot be lifted
  def isImplemented(procs: Map[(Name, Int), Proc], expr: Expr): Boolean =
    expr.funs.exists(fun => procs.contains((fun.name, fun.arity)))

  // the program with the implemented functions in its executed expressions replaced by calls
  def impl(state: State, procs: Map[(Name, Int), Proc], prog: Prog): Prog =
    prog match
      case Assign(lhs, rhs) =>
        val (xs, pre, rhs_) = lift(state, procs, rhs)
        block(xs, pre, Assign(lhs, rhs_))

      case Call(name, args, res) =>
        val (xs, pre, args_) = lift(state, procs, args)
        block(xs, pre, Call(name, args_, res))

      case If(test, left, right) =>
        val (xs, pre, test_) = lift(state, procs, test)
        block(xs, pre, If(test_, impl(state, procs, left), impl(state, procs, right)))

      // the guard is evaluated anew at the beginning of each iteration, including after continue;
      // the attributes of blocks and loops are specifications
      case While(test, body, attrs) =>
        val (xs, pre, test_) = lift(state, procs, test)
        val body_ = impl(state, procs, body)
        if pre.isEmpty
        then While(test, body_, attrs)
        else Iter(Block(xs, pre ++ List(If(Not(test_), Break, Skip), body_)), attrs)

      case Block(locals, progs, attrs) =>
        Block(locals, progs.map(impl(state, procs, _)), attrs)

      case Iter(body, attrs) =>
        Iter(impl(state, procs, body), attrs)

      case Choice(progs) =>
        Choice(progs.map(impl(state, procs, _)))

      case Par(progs) =>
        Par(progs.map(impl(state, procs, _)))

      // assertions, assumptions, and the right-hand sides of differential equations are specifications
      case _: Spec | _: Ode | Break | Continue | Return =>
        prog

  // `prog` after the statements `pre` in the scope of the locals `xs`
  def block(xs: List[Var], pre: List[Prog], prog: Prog): Prog =
    if pre.isEmpty
    then prog
    else Block(xs, pre ++ List(prog))

  // the expressions `exprs` evaluated from left to right
  def lift(state: State, procs: Map[(Name, Int), Proc], exprs: List[Expr]): (List[Var], List[Prog], List[Expr]) =
    val lifted = exprs.map(lift(state, procs, _))
    (lifted.flatMap(_._1), lifted.flatMap(_._2), lifted.map(_._3))

  // the fresh locals and the statements that compute the implemented functions of `expr`, and `expr` over these locals,
  // none if `expr` applies no implemented function
  def lift(state: State, procs: Map[(Name, Int), Proc], expr: Expr): (List[Var], List[Prog], Expr) =
    expr match
      case _: Var | _: Lit =>
        (Nil, Nil, expr)

      case App(Fun.and, _, _, List(left, right)) =>
        conditional(state, procs, Fun.and, left, right, true, False)

      case App(Fun.or, _, _, List(left, right)) =>
        conditional(state, procs, Fun.or, left, right, false, True)

      case App(Fun.imp, _, _, List(left, right)) =>
        conditional(state, procs, Fun.imp, left, right, true, True)

      // a conditional only if a branch calls an implementation
      case Ite(test, left, right) =>
        val (xs0, pre0, test_) = lift(state, procs, test)
        val (xs1, pre1, left_) = lift(state, procs, left)
        val (xs2, pre2, right_) = lift(state, procs, right)

        if pre1.isEmpty && pre2.isEmpty
        then (xs0, pre0, Ite(test_, left_, right_))
        else
          val res = Var(Name("test", None), expr.typ).fresh
          val ite = If(test_, block(xs1, pre1, Assign(List(res), List(left_))), block(xs2, pre2, Assign(List(res), List(right_))))
          (xs0 ++ List(res), pre0 ++ List(ite), res)

      case App(fun, _, typ, args) if procs.contains((fun.name, fun.arity)) =>
        val proc = procs((fun.name, fun.arity))
        val (xs, pre, args_) = lift(state, procs, args)

        Error.report("the signature of the implementing procedure does not admit the application", proc, expr):
          Type.bind(state, proc.args ++ proc.res, args.types ++ List(typ))

        val res = Var(Name("test", None), typ).fresh
        (xs ++ List(res), pre ++ List(Call(proc.name, args_, List(res))), res)

      case App(fun, inst, typ, args) =>
        val (xs, pre, args_) = lift(state, procs, args)
        (xs, pre, App(fun, inst, typ, args_))

      case Distinct(exprs) =>
        val (xs, pre, exprs_) = lift(state, procs, exprs)
        (xs, pre, Distinct(exprs_))

      case Is(arg, fun) =>
        val (xs, pre, arg_) = lift(state, procs, arg)
        (xs, pre, Is(arg_, fun))

      case As(arg, typ) =>
        val (xs, pre, arg_) = lift(state, procs, arg)
        (xs, pre, As(arg_, typ))

      // the arguments of let and match are evaluated before the binding
      case Let(bound, args, body) if !isImplemented(procs, body) =>
        val (xs, pre, args_) = lift(state, procs, args)
        (xs, pre, Let(bound, args_, body))

      case Match(arg, cases) if !cases.exists(c => isImplemented(procs, c.body) || isImplemented(procs, c.cond)) =>
        val (xs, pre, arg_) = lift(state, procs, arg)
        (xs, pre, Match(arg_, cases))

      case _ if isImplemented(procs, expr) =>
        Error.raise("implemented functions under binders or old are not supported", expr)

      case _ =>
        (Nil, Nil, expr)

  // the operator `fun` of `left` and `right`, whose right operand is evaluated only if the left one is `needed` (true
  // or false), and whose value is `short` otherwise: as is if the right operand calls no implementation, otherwise a
  // fresh boolean assigned by a conditional on the left operand
  def conditional(state: State, procs: Map[(Name, Int), Proc], fun: Fun, left: Expr, right: Expr, needed: Boolean, short: Expr): (List[Var], List[Prog], Expr) =
    val (xs1, pre1, left_) = lift(state, procs, left)
    val (xs2, pre2, right_) = lift(state, procs, right)

    if pre2.isEmpty
    then (xs1, pre1, App(fun, List(left_, right_)))
    else
      val res = Var(Name("test", None), Sort.bool).fresh
      val evaluated = block(xs2, pre2, Assign(List(res), List(right_)))
      val skipped = Assign(List(res), List(short))
      val cond = if needed then If(left_, evaluated, skipped) else If(left_, skipped, evaluated)
      (xs1 ++ List(res), pre1 ++ List(cond), res)
