package cuvee.transform

import util.Name
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._

// implementations of functions by functions and methods with the attribute :implement, whose value, the pattern, is
// the implemented function applied to a permutation of the inputs of the implementation, e.g. x in this for a member
// of a datatype that defines the sort of sets (see ideas/implementations.md);
// - an implementation by a function replaces the applications of the implemented function everywhere: in programs,
//   contracts, invariants, function bodies, axioms, and lemmas, since the abstract functions have no meaning on the
//   datatypes that define their sorts, except in the implementations themselves;
// - an implementation by a method, which has a single output, the result, may be nondeterministic: the applications
//   of the implemented function in the expressions that programs execute become calls, in the order of evaluation,
//   whose results are fresh locals, such that each evaluation chooses anew; the right operands of && || ==> and the
//   branches of ite are evaluated only if they are needed, as are their calls, which become conditionals, and the
//   calls of a loop guard are made before each test, the loop becomes an iteration that breaks if the guard is false,
//   whose invariants hold at the beginning of each iteration, before these calls; applications in specifications,
//   which are deterministic, under binders, which bind variables of the arguments, and under old, which evaluates
//   them in another state, are errors
object Implement extends Transform:
  // the entry of the implementations, injected before the modules of -include implement:<name> (see Config.features),
  // with the source that parses it
  val modules =
    List((cuvee.dafny.Source, "/cuvee/implement.dfy"))

  // an implementation by function `fun`, whose inputs are the arguments of the implemented function at `positions`
  case class ByFunction(fun: Fun, positions: List[Int])

  // an implementation by procedure `proc`, whose inputs are the arguments of the implemented function at `positions`
  case class ByMethod(proc: Proc, positions: List[Int])

  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Option[Cmd]): (List[Cmd], Option[Cmd]) =
    val (funs, methods) = implementations(state)

    val cmds_ =
      for cmd <- cmds
      yield cmd match
        case decl: Decl if decl.attrs.isImplementation =>
          cmd

        case _ if funs.isEmpty && methods.isEmpty =>
          cmd

        case _ =>
          cmd.map(expr(state, funs, _), prog(state, funs, _)) match
            case DefineProc(proc, body, attrs) =>
              specification(methods, attrs.funs)
              DefineProc(proc, implement(methods, body), attrs)

            case cmd_ =>
              specification(methods, cmd_.funs)
              cmd_

    (cmds_, last)

  // the implementations by the functions that they implement, by functions and by methods, at most one each
  def implementations(state: State): (Map[Fun, ByFunction], Map[Fun, ByMethod]) =
    val funs =
      for
        (key, attrs) <- state.funattrs.toList
        pattern <- attrs.values[Expr]("implement")
      yield
        val fun = state.funs(key)
        val (implemented, positions_) = positions(fun.name, pattern, fun.formals)
        implemented -> ByFunction(fun, positions_)

    val methods =
      for
        (name, attrs) <- state.procattrs.toList
        pattern <- attrs.values[Expr]("implement")
      yield
        val proc = state.procs(name)

        Error.report("an implementing method has a single output", name.subscripted):
          require(proc.out.length == 1)

        val (implemented, positions_) = positions(name, pattern, proc.in)
        implemented -> ByMethod(proc, positions_)

    val implemented = funs.map(_._1) ++ methods.map(_._1)
    Error.report("functions with several implementations", implemented.diff(implemented.distinct).map(_.name.subscripted)*):
      require(implemented.distinct.length == implemented.length)

    (funs.toMap, methods.toMap)

  // the implemented function of `pattern` of implementation `name` and the positions of the inputs `in` among its
  // arguments, which must be all inputs, each once
  def positions(name: Name, pattern: Expr, in: List[Var]): (Fun, List[Int]) =
    pattern match
      case App(fun, _, _, args) =>
        val xs =
          for arg <- args
          yield arg match
            case x: Var if in.contains(x) => x
            case _                        => Error.raise("the arguments of a pattern must be inputs", name.subscripted)

        Error.report("the inputs in a pattern must be distinct", name.subscripted):
          require(xs.distinct == xs)

        Error.report("a pattern must contain all inputs", name.subscripted):
          require(in.diff(xs).isEmpty)

        (fun, in.map(xs.indexOf))

      case _ =>
        Error.raise("a pattern must be an application", name.subscripted)

  // the program with the applications of functions implemented by functions replaced in all its expressions,
  // including those of the attributes, e.g. invariants
  def prog(state: State, funs: Map[Fun, ByFunction], prog_ : Prog): Prog =
    prog_.map(expr(state, funs, _), prog(state, funs, _))

  // the expression with the applications of functions implemented by functions replaced, bottom-up
  def expr(state: State, funs: Map[Fun, ByFunction], expr_ : Expr): Expr =
    expr_.map(expr(state, funs, _)) match
      case App(fun, _, _, args) if funs.contains(fun) =>
        val ByFunction(impl, positions) = funs(fun)
        App(state, impl, positions.map(args))

      case expr__ =>
        expr__

  // the names of the functions among `used` that are implemented by methods
  def implemented(methods: Map[Fun, ByMethod], used: Iterable[Fun]): List[String] =
    used.filter(methods.contains).map(_.name.subscripted).toList.distinct

  // functions implemented by methods are nondeterministic, hence they must not occur in specifications, whose
  // functions `used` are given
  def specification(methods: Map[Fun, ByMethod], used: Iterable[Fun]): Unit =
    val names = implemented(methods, used)
    Error.report("functions implemented by methods in a specification", names*):
      require(names.isEmpty)

  // whether one of the functions `used` is implemented by a method, needed only where applications cannot be lifted
  def isImplemented(methods: Map[Fun, ByMethod], used: Iterable[Fun]): Boolean =
    used.exists(methods.contains)

  // the program with the applications of functions implemented by methods in its executed expressions replaced by
  // calls, and none in its specifications
  def implement(methods: Map[Fun, ByMethod], prog: Prog): Prog =
    prog match
      case Assign(lhs, rhs) =>
        val (xs, pre, rhs_) = lift(methods, rhs)
        block(xs, pre, Assign(lhs, rhs_))

      case Call(name, args, res) =>
        val (xs, pre, args_) = lift(methods, args)
        block(xs, pre, Call(name, args_, res))

      case If(test, left, right) =>
        val (xs, pre, test_) = lift(methods, test)
        block(xs, pre, If(test_, implement(methods, left), implement(methods, right)))

      // the guard is evaluated anew at the beginning of each iteration, including after continue
      case While(test, body, attrs) =>
        specification(methods, attrs.funs)
        val (xs, pre, test_) = lift(methods, test)
        val body_ = implement(methods, body)
        if pre.isEmpty
        then While(test, body_, attrs)
        else Iter(Block(xs, pre ++ List(If(Not(test_), Break, Skip), body_)), attrs)

      case Block(locals, progs, attrs) =>
        specification(methods, attrs.funs)
        Block(locals, progs.map(implement(methods, _)), attrs)

      case Iter(body, attrs) =>
        specification(methods, attrs.funs)
        Iter(implement(methods, body), attrs)

      case Choice(progs) =>
        Choice(progs.map(implement(methods, _)))

      case Par(progs) =>
        Par(progs.map(implement(methods, _)))

      // assertions, assumptions, and the differential equations are specifications
      case _: Spec | _: Ode =>
        specification(methods, prog.funs)
        prog

      case Break | Continue | Return =>
        prog

  // `prog` after the statements `pre` in the scope of the locals `xs`
  def block(xs: List[Var], pre: List[Prog], prog: Prog): Prog =
    if pre.isEmpty
    then prog
    else Block(xs, pre ++ List(prog))

  // the expressions `exprs` evaluated from left to right
  def lift(methods: Map[Fun, ByMethod], exprs: List[Expr]): (List[Var], List[Prog], List[Expr]) =
    val lifted = exprs.map(lift(methods, _))
    (lifted.flatMap(_._1), lifted.flatMap(_._2), lifted.map(_._3))

  // the fresh locals and the statements that call the implementations of the functions of `expr`, and `expr` over
  // these locals, none if `expr` applies no function implemented by a method
  def lift(methods: Map[Fun, ByMethod], expr: Expr): (List[Var], List[Prog], Expr) =
    expr match
      case _: Var | _: Lit =>
        (Nil, Nil, expr)

      case App(Fun.and, _, _, List(left, right)) =>
        conditional(methods, Fun.and, left, right, true, False)

      case App(Fun.or, _, _, List(left, right)) =>
        conditional(methods, Fun.or, left, right, false, True)

      case App(Fun.imp, _, _, List(left, right)) =>
        conditional(methods, Fun.imp, left, right, true, True)

      // a conditional only if a branch calls an implementation
      case Ite(test, left, right) =>
        val (xs0, pre0, test_) = lift(methods, test)
        val (xs1, pre1, left_) = lift(methods, left)
        val (xs2, pre2, right_) = lift(methods, right)

        if pre1.isEmpty && pre2.isEmpty
        then (xs0, pre0, Ite(test_, left_, right_))
        else
          val res = Var(Name("test", None), expr.typ).fresh
          val ite = If(test_, block(xs1, pre1, Assign(List(res), List(left_))), block(xs2, pre2, Assign(List(res), List(right_))))
          (xs0 ++ List(res), pre0 ++ List(ite), res)

      // the arguments at the positions of the inputs of the method
      case App(fun, _, typ, args) if methods.contains(fun) =>
        val ByMethod(proc, positions) = methods(fun)
        val (xs, pre, args_) = lift(methods, args)
        val res = Var(Name("test", None), typ).fresh
        val call = Call(proc.name, positions.map(args_), List(res))
        (xs ++ List(res), pre ++ List(call), res)

      case App(fun, inst, typ, args) =>
        val (xs, pre, args_) = lift(methods, args)
        (xs, pre, App(fun, inst, typ, args_))

      case Distinct(exprs) =>
        val (xs, pre, exprs_) = lift(methods, exprs)
        (xs, pre, Distinct(exprs_))

      case Is(arg, fun) =>
        val (xs, pre, arg_) = lift(methods, arg)
        (xs, pre, Is(arg_, fun))

      case As(arg, typ) =>
        val (xs, pre, arg_) = lift(methods, arg)
        (xs, pre, As(arg_, typ))

      // the arguments of let and match are evaluated before the binding
      case Let(bound, args, body) if !isImplemented(methods, body.funs) =>
        val (xs, pre, args_) = lift(methods, args)
        (xs, pre, Let(bound, args_, body))

      case Match(arg, cases) if !isImplemented(methods, cases.funs) =>
        val (xs, pre, arg_) = lift(methods, arg)
        (xs, pre, Match(arg_, cases))

      case _ if isImplemented(methods, expr.funs) =>
        Error.raise("functions implemented by methods under binders or old are not supported", implemented(methods, expr.funs)*)

      case _ =>
        (Nil, Nil, expr)

  // the operator `fun` of `left` and `right`, whose right operand is evaluated only if the left one is `needed` (true
  // or false), and whose value is `short` otherwise: as is if the right operand calls no implementation, otherwise a
  // fresh boolean assigned by a conditional on the left operand
  def conditional(methods: Map[Fun, ByMethod], fun: Fun, left: Expr, right: Expr, needed: Boolean, short: Expr): (List[Var], List[Prog], Expr) =
    val (xs1, pre1, left_) = lift(methods, left)
    val (xs2, pre2, right_) = lift(methods, right)

    if pre2.isEmpty
    then (xs1, pre1, App(fun, List(left_, right_)))
    else
      val res = Var(Name("test", None), Sort.bool).fresh
      val evaluated = block(xs2, pre2, Assign(List(res), List(right_)))
      val skipped = Assign(List(res), List(short))
      val cond = if needed then If(left_, evaluated, skipped) else If(left_, skipped, evaluated)
      (xs1 ++ List(res), pre1 ++ List(cond), res)
