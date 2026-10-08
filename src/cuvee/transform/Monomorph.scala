package cuvee.transform

import scala.collection.mutable

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
  // poly: the polymorphic functions of the input with their declaration or definition,
  // instances: the instances emitted so far, out: the output
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val poly = polymorphic(config.output.features, prefix ++ cmds)
    val instances = Ref(Map[(Name, Int, List[Type]), Fun]())
    val out = mutable.ListBuffer[Cmd]()

    // the instances emitted for the commands before are known, their output is discarded
    prefix.foreach(command(state, poly, instances, out, _))
    out.clear()

    cmds.foreach(command(state, poly, instances, out, _))
    out.toList

  // the polymorphic functions of `cmds` with their declaration or definition,
  // except those that the receiver of the output knows, e.g. = and select of SMT-LIB (see Sink.known)
  def polymorphic(features: Set[String], cmds: List[Cmd]): Map[(Name, Int), Cmd] =
    val decls =
      cmds.collect:
        case cmd @ DeclareFun(fun, attrs) if fun.params.nonEmpty && !features.exists(attrs.contains)   => (fun.name, fun.arity) -> cmd
        case cmd @ DefineFun(fun, _, attrs) if fun.params.nonEmpty && !features.exists(attrs.contains) => (fun.name, fun.arity) -> cmd
    decls.toMap

  // the name of an instance, e.g. length<Elem> and select<Int,Array<Int,Bool>>
  def name(fun: Fun, types: List[Type]): Name =
    Name(fun.name.name + "<" + types.map(show).mkString(",") + ">", fun.name.index)

  def show(typ: Type): String =
    typ match
      case Param(name)     => name.indexed
      case BitVec(n)       => "bv" + n
      case Sort(con, Nil)  => con.name.indexed
      case Sort(con, args) => con.name.indexed + "<" + args.map(show).mkString(",") + ">"

  def isPoly(poly: Map[(Name, Int), Cmd], fun: Fun) =
    fun.params.nonEmpty && poly.contains((fun.name, fun.arity))

  def emit(out: mutable.ListBuffer[Cmd], cmd: Cmd): Unit =
    out += cmd

  def command(state: State, poly: Map[(Name, Int), Cmd], instances: Ref[Map[(Name, Int, List[Type]), Fun]], out: mutable.ListBuffer[Cmd], cmd: Cmd): Unit =
    cmd match
      case DeclareFun(fun, _) if isPoly(poly, fun) =>

      case DefineFun(fun, _, _) if isPoly(poly, fun) =>

      case DefineFun(fun, body, attrs) =>
        val body_ = expr(state, poly, instances, out, body)
        emit(out, DefineFun(fun, body_, attrs))

      case Assert(justify, params, phi, attrs) =>
        val phi_ = expr(state, poly, instances, out, phi)
        emit(out, Assert(justify, params, phi_, attrs))

      case _ =>
        emit(out, cmd)

  // the monomorphic instance of `fun` for the instances `types` of its type parameters,
  // which is emitted on first use, after the instances that its body uses
  def instance(state: State, poly: Map[(Name, Int), Cmd], instances: Ref[Map[(Name, Int, List[Type]), Fun]], out: mutable.ListBuffer[Cmd], fun: Fun, types: List[Type]): Fun =
    val key = (fun.name, fun.arity, types)

    instances.value.get(key) match
      case Some(fun_) =>
        fun_

      case None =>
        val su = Subst.from(fun.params, types)
        val fun_ = Fun(name(fun, types), Nil, fun.formals.map(x => Var(x.name, su(x.typ))), su(fun.res))
        instances := instances.value + (key -> fun_)

        poly((fun.name, fun.arity)) match
          case DeclareFun(_, attrs) =>
            emit(out, DeclareFun(fun_, attrs))

          case DefineFun(_, body, attrs) =>
            val body_ = expr(state, poly, instances, out, su(body))
            emit(out, DefineFun(fun_, body_, attrs))

          case cmd =>
            Error.raise("not a function", cmd)

        fun_

  // applications of polymorphic functions are replaced by their instances,
  // whose type parameters are determined by the types of the arguments and of the result,
  // in which defined sorts are expanded (see Type.expand), such that each instance is named after the sorts of its definition
  def expr(state: State, poly: Map[(Name, Int), Cmd], instances: Ref[Map[(Name, Int, List[Type]), Fun]], out: mutable.ListBuffer[Cmd], e: Expr): Expr =
    e match
      case App(fun, inst, typ, args) if isPoly(poly, fun) =>
        val su = Type.bind(state, fun.args :+ fun.res, inst :+ typ)
        val types = fun.params.map(su(_))

        Error.report("instance of polymorphic function is not monomorphic", fun, types):
          require(types.params.isEmpty)

        // the instance is emitted before those of the arguments
        val fun_ = instance(state, poly, instances, out, fun, types)
        val args_ = args.map(expr(state, poly, instances, out, _))
        App(fun_, inst, typ, args_)

      // instances of polymorphic constants need no annotation of their type
      case As(arg @ App(fun, _, _, Nil), typ) if isPoly(poly, fun) =>
        expr(state, poly, instances, out, arg)

      case _ =>
        e.map(expr(state, poly, instances, out, _))
