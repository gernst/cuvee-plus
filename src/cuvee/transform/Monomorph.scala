package cuvee.transform

import util.Name
import util.Ref
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._

// monomorphization of polymorphic functions, which the solvers do not accept:
// the polymorphic declarations and definitions of functions in the input are dropped,
// and each instance that is used is declared or defined right before the first command that uses it,
// named after the function and the instances of its type parameters, e.g. length<Elem>;
// polymorphic datatypes and sorts are kept, which the solvers accept,
// as are polymorphic assertions, which are not instantiated (see TODO.md)
object Monomorph extends Transform:
  // the polymorphic functions of the input with their declaration or definition,
  // the instances emitted so far, and the output
  case class Env(poly: Map[(Name, Int), Cmd], instances: Ref[Map[(Name, Int, List[Type]), Fun]], out: Ref[List[Cmd]])

  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val env = Env(polymorphic(prefix ++ cmds), Ref(Map()), Ref(Nil))

    // the instances emitted for the commands before are known, their output is discarded
    prefix.foreach(command(env, _))
    env.out := Nil

    cmds.foreach(command(env, _))
    env.out.value

  // the polymorphic functions of `cmds` with their declaration or definition
  def polymorphic(cmds: List[Cmd]): Map[(Name, Int), Cmd] =
    val decls =
      cmds.collect:
        case cmd @ DeclareFun(fun, _) if fun.params.nonEmpty    => (fun.name, fun.arity) -> cmd
        case cmd @ DefineFun(fun, _, _) if fun.params.nonEmpty  => (fun.name, fun.arity) -> cmd
    decls.toMap

  // the name of an instance, e.g. length<Elem> and select<Int,Array<Int,Bool>>
  def name(fun: Fun, types: List[Type]): Name =
    Name(fun.name.name + "<" + types.map(show).mkString(",") + ">", fun.name.index)

  def show(typ: Type): String =
    typ match
      case Param(name)     => name.indexed
      case Sort(con, Nil)  => con.name.indexed
      case Sort(con, args) => con.name.indexed + "<" + args.map(show).mkString(",") + ">"

  def isPoly(env: Env, fun: Fun) =
    fun.params.nonEmpty && env.poly.contains((fun.name, fun.arity))

  def emit(env: Env, cmd: Cmd): Unit =
    env.out := env.out.value :+ cmd

  def command(env: Env, cmd: Cmd): Unit =
    cmd match
      case DeclareFun(fun, _) if isPoly(env, fun) =>

      case DefineFun(fun, _, _) if isPoly(env, fun) =>

      case DefineFun(fun, body, attrs) =>
        val body_ = expr(env, body)
        emit(env, DefineFun(fun, body_, attrs))

      case Assert(justify, params, phi, attrs) =>
        val phi_ = expr(env, phi)
        emit(env, Assert(justify, params, phi_, attrs))

      case _ =>
        emit(env, cmd)

  // the monomorphic instance of `fun` for the instances `types` of its type parameters,
  // which is emitted on first use, after the instances that its body uses
  def instance(env: Env, fun: Fun, types: List[Type]): Fun =
    val key = (fun.name, fun.arity, types)

    env.instances.value.get(key) match
      case Some(fun_) =>
        fun_

      case None =>
        val su = Subst.from(fun.params, types)
        val fun_ = Fun(name(fun, types), Nil, fun.formals.map(x => Var(x.name, su(x.typ))), su(fun.res))
        env.instances := env.instances.value + (key -> fun_)

        env.poly((fun.name, fun.arity)) match
          case DeclareFun(_, attrs) =>
            emit(env, DeclareFun(fun_, attrs))

          case DefineFun(_, body, attrs) =>
            val body_ = expr(env, su(body))
            emit(env, DefineFun(fun_, body_, attrs))

          case cmd =>
            Error.raise("not a function", cmd)

        fun_

  // applications of polymorphic functions are replaced by their instances,
  // whose type parameters are determined by the types of the arguments and of the result
  def expr(env: Env, e: Expr): Expr =
    e match
      case _: Var | _: Lit =>
        e

      case App(fun, inst, typ, args) if isPoly(env, fun) =>
        val su = Type.bind(fun.args :+ fun.res, inst :+ typ)
        val types = fun.params.map(su(_))

        Error.report("instance of polymorphic function is not monomorphic", fun, types):
          require(types.params.isEmpty)

        // the instance is emitted before those of the arguments
        val fun_ = instance(env, fun, types)
        val args_ = args.map(expr(env, _))
        App(fun_, inst, typ, args_)

      case App(fun, inst, typ, args) =>
        val args_ = args.map(expr(env, _))
        App(fun, inst, typ, args_)

      case Distinct(exprs) =>
        val exprs_ = exprs.map(expr(env, _))
        Distinct(exprs_)

      case Is(arg, fun) =>
        val arg_ = expr(env, arg)
        Is(arg_, fun)

      // instances of polymorphic constants need no annotation of their type
      case As(arg @ App(fun, _, _, Nil), typ) if isPoly(env, fun) =>
        expr(env, arg)

      case As(arg, typ) =>
        val arg_ = expr(env, arg)
        As(arg_, typ)

      case Diff(xs, arg) =>
        val arg_ = expr(env, arg)
        Diff(xs, arg_)

      case Old(arg) =>
        val arg_ = expr(env, arg)
        Old(arg_)

      case Trace(init, deps, acc, bound, updates) =>
        val init_ = expr(env, init)
        val deps_ = deps.map(expr(env, _))
        val updates_ = for Upd(cond, rhs) <- updates yield Upd(expr(env, cond), expr(env, rhs))
        Trace(init_, deps_, acc, bound, updates_)

      case Maps(deps, bound, updates) =>
        val deps_ = deps.map(expr(env, _))
        val updates_ = for Upd(cond, rhs) <- updates yield Upd(expr(env, cond), expr(env, rhs))
        Maps(deps_, bound, updates_)

      case Invs(deps, bound, body) =>
        val deps_ = deps.map(expr(env, _))
        val body_ = expr(env, body)
        Invs(deps_, bound, body_)

      case Bind(quant, bound, body) =>
        val body_ = expr(env, body)
        Bind(quant, bound, body_)

      case Let(bound, args, body) =>
        val args_ = args.map(expr(env, _))
        val body_ = expr(env, body)
        Let(bound, args_, body_)
