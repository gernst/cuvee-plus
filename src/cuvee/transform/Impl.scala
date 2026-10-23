package cuvee.transform

import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._

// implementations of functions by functions with the attribute :implements, whose value, the pattern, is the
// implemented function applied to a permutation of the inputs of the implementation, e.g. x in this for a member of
// a datatype that defines the sort of sets (see ideas/implementations.md); the applications of the implemented
// functions are replaced by those of their implementations, with the arguments at the positions of the pattern,
// everywhere: in programs, contracts, invariants, function bodies, axioms, and lemmas, since the abstract functions
// have no meaning on the datatypes that define their sorts, except in the implementations themselves; an
// implementation with an input that is not in its pattern reads a nondeterministic value, which is not supported yet
object Impl extends Transform:
  // the entry of the implementations, injected before the modules of -include impl:<name> (see Config.features),
  // with the source that parses it
  val modules =
    List((cuvee.dafny.Source, "/cuvee/impl.dfy"))

  // an implementation `impl` of a function with the inputs of `impl` in the order of the arguments of the function
  case class Implementation(impl: Fun, pattern: List[Var])

  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Option[Cmd]): (List[Cmd], Option[Cmd]) =
    val impls = implementations(state)

    val cmds_ =
      for cmd <- cmds
      yield cmd match
        case DeclareFun(_, attrs) if attrs.isImplementation =>
          cmd

        case DefineFun(_, _, attrs) if attrs.isImplementation =>
          cmd

        case _ if impls.isEmpty =>
          cmd

        case _ =>
          cmd.map(expr(state, impls, _), prog(state, impls, _))

    (cmds_, last)

  // the implementations by the functions that they implement, whose patterns are applications to distinct inputs,
  // all of them or all but one
  def implementations(state: State): Map[Fun, Implementation] =
    val entries =
      for
        (key, attrs) <- state.funattrs.toList
        pattern <- attrs.values[Expr]("implements")
      yield
        val impl = state.funs(key)

        pattern match
          case App(fun, _, _, args) =>
            val xs =
              for arg <- args
              yield arg match
                case x: Var if impl.formals.contains(x) => x
                case _                                  => Error.raise("the arguments of a pattern must be inputs", impl.name, arg)

            Error.report("the inputs in a pattern must be distinct", impl.name, xs):
              require(xs.distinct == xs)

            Error.report("a pattern must contain all inputs, or all but the one of a nondeterministic value", impl.name, impl.formals.diff(xs)):
              require(impl.formals.diff(xs).length <= 1)

            fun -> Implementation(impl, xs)

          case _ =>
            Error.raise("a pattern must be an application", impl.name, pattern)

    val funs = entries.map(_._1)
    Error.report("functions with several implementations", funs.diff(funs.distinct).map(_.name)):
      require(funs.distinct.length == funs.length)

    entries.toMap

  // the program with the expressions replaced, including those of the attributes, e.g. invariants
  def prog(state: State, impls: Map[Fun, Implementation], prog_ : Prog): Prog =
    prog_.map(expr(state, impls, _), prog(state, impls, _))

  // the expression with the applications of implemented functions replaced, bottom-up
  def expr(state: State, impls: Map[Fun, Implementation], expr_ : Expr): Expr =
    expr_.map(expr(state, impls, _)) match
      case App(fun, _, _, args) if impls.contains(fun) =>
        val Implementation(impl, pattern) = impls(fun)

        Error.report("nondeterministic implementations are not supported yet", impl.name):
          require(impl.formals.forall(pattern.contains))

        App(state, impl, impl.formals.map(x => args(pattern.indexOf(x))))

      case expr__ =>
        expr__
