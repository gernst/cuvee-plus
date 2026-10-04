package cuvee.transform

import scala.collection.mutable

import util.Name
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
  def apply(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State): List[Cmd] =
    val mono = new Monomorph(prefix ++ cmds)

    // the instances emitted for the commands before are known, their output is discarded
    prefix.foreach(mono.command)
    mono.out.clear()

    cmds.foreach(mono.command)
    mono.out.toList

  // the name of an instance, e.g. length<Elem> and select<Int,Array<Int,Bool>>
  def name(fun: Fun, types: List[Type]): Name =
    Name(fun.name.name + "<" + types.map(show).mkString(",") + ">", fun.name.index)

  def show(name: Name): String =
    name match
      case Name(name, None)        => name
      case Name(name, Some(index)) => name + "$" + index

  def show(typ: Type): String =
    typ match
      case Param(name)     => show(name)
      case Sort(con, Nil)  => show(con.name)
      case Sort(con, args) => show(con.name) + "<" + args.map(show).mkString(",") + ">"

class Monomorph(cmds: List[Cmd]):
  // the polymorphic functions of the input with their declaration or definition
  val poly: Map[(Name, Int), Cmd] =
    val decls =
      cmds.collect:
        case cmd @ DeclareFun(fun, _) if fun.params.nonEmpty    => (fun.name, fun.arity) -> cmd
        case cmd @ DefineFun(fun, _, _) if fun.params.nonEmpty  => (fun.name, fun.arity) -> cmd
    decls.toMap

  // the instances emitted so far, and the output
  val instances = mutable.Map[(Name, Int, List[Type]), Fun]()
  val out = mutable.ListBuffer[Cmd]()

  def isPoly(fun: Fun) =
    fun.params.nonEmpty && poly.contains((fun.name, fun.arity))

  def command(cmd: Cmd): Unit =
    cmd match
      case DeclareFun(fun, _) if isPoly(fun) =>

      case DefineFun(fun, _, _) if isPoly(fun) =>

      case DefineFun(fun, body, attrs) =>
        val body_ = expr(body)
        out += DefineFun(fun, body_, attrs)

      case Assert(justify, params, phi, attrs) =>
        val phi_ = expr(phi)
        out += Assert(justify, params, phi_, attrs)

      case _ =>
        out += cmd

  // the monomorphic instance of `fun` for the instances `types` of its type parameters,
  // which is emitted on first use, after the instances that its body uses
  def instance(fun: Fun, types: List[Type]): Fun =
    val key = (fun.name, fun.arity, types)

    instances.get(key) match
      case Some(fun_) =>
        fun_

      case None =>
        val su = Subst.from(fun.params, types)
        val fun_ = Fun(Monomorph.name(fun, types), Nil, fun.formals.map(x => Var(x.name, su(x.typ))), su(fun.res))
        instances(key) = fun_

        poly((fun.name, fun.arity)) match
          case DeclareFun(_, attrs) =>
            out += DeclareFun(fun_, attrs)

          case DefineFun(_, body, attrs) =>
            val body_ = expr(su(body))
            out += DefineFun(fun_, body_, attrs)

          case cmd =>
            Error.raise("not a function", cmd)

        fun_

  // applications of polymorphic functions are replaced by their instances,
  // whose type parameters are determined by the types of the arguments and of the result
  def expr(e: Expr): Expr =
    e match
      case _: Var | _: Lit =>
        e

      case App(fun, inst, typ, args) if isPoly(fun) =>
        val su = Type.bind(fun.args :+ fun.res, inst :+ typ)
        val types = fun.params.map(su(_))

        Error.report("instance of polymorphic function is not monomorphic", fun, types):
          require(types.params.isEmpty)

        App(instance(fun, types), inst, typ, args.map(expr))

      case App(fun, inst, typ, args) =>
        App(fun, inst, typ, args.map(expr))

      case Distinct(exprs) =>
        Distinct(exprs.map(expr))

      case Is(arg, fun) =>
        Is(expr(arg), fun)

      // instances of polymorphic constants need no annotation of their type
      case As(arg @ App(fun, _, _, Nil), typ) if isPoly(fun) =>
        expr(arg)

      case As(arg, typ) =>
        As(expr(arg), typ)

      case Diff(xs, arg) =>
        Diff(xs, expr(arg))

      case Old(arg) =>
        Old(expr(arg))

      case Bind(quant, bound, body) =>
        Bind(quant, bound, expr(body))

      case Let(bound, args, body) =>
        Let(bound, args.map(expr), expr(body))
