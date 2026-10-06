package cuvee.core

import scala.annotation.targetName
import util.Name
import cuvee.Error

extension (self: List[Param])
  @targetName("Params.fresh")
  def fresh = self.map(_.fresh)

  @targetName("Params.asIndex")
  def asIndex = self.map(_.asIndex)

extension (self: List[Var])
  @targetName("Vars.fresh")
  def fresh = self.map(_.fresh)

  @targetName("Vars.asPairs")
  def asPairs = self.map(_.asPair)

  @targetName("Vars.asIndex")
  def asIndex = self.map(_.asIndex)

extension (self: Iterable[Type])
  @targetName("Types.params")
  def params = self.flatMap(_.params).toSet

  @targetName("Types.cons")
  def cons = self.flatMap(_.cons).toSet

extension (self: Iterable[Expr])
  @targetName("Exprs.free")
  def free = self.flatMap(_.free).toSet

  @targetName("Exprs.params")
  def params = self.flatMap(_.params).toSet

extension (self: Iterable[Upd])
  @targetName("Upds.free")
  def free = self.flatMap(_.free).toSet

  @targetName("Upds.params")
  def params = self.flatMap(_.params).toSet

  def guards = self.map(_.cond).toList

extension (self: Iterable[Case])
  @targetName("Cases.free")
  def free = self.flatMap(_.free).toSet

  @targetName("Cases.params")
  def params = self.flatMap(_.params).toSet

extension (self: Iterable[Prog])
  @targetName("Progs.mod")
  def mod = self.flatMap(_.mod).toSet

extension (self: List[Type])
  @targetName("Types.sig")
  def sig = self.map(_.sig)

extension (self: List[Expr])
  @targetName("Exprs.types")
  def types = self.map(_.typ)

  // the arguments of a conjunction of `self`, flattened, without true and without duplicates
  @targetName("Exprs.conjuncts")
  def conjuncts = self.flatMap(And.flattenStrong).distinct

  // the arguments of a disjunction of `self`, flattened, without false and without duplicates
  @targetName("Exprs.disjuncts")
  def disjuncts = self.flatMap(Or.flattenStrong).distinct

class Quant(val name: Name):
  // SMT-LIB does not admit quantifiers without bound variables
  def apply(bound: List[Var], body: Expr): Expr =
    if bound.isEmpty
    then body
    else Bind(name, bound, body)

  def unapply(expr: Expr) =
    expr match
      case Bind(`name`, bound, body) =>
        Some((bound, body))

      case _ =>
        None

object All extends Quant("forall")
object Ex extends Quant("exists")

enum Assoc:
  case Left, Right

  def reduce[A](xs: Iterable[A], f: (A, A) => A): A =
    this match
      case Left  => xs.reduceLeft(f)
      case Right => xs.reduceRight(f)

object Sugar:
  // calls of the procedure `name` with `in` arguments and `out` results
  class call(val name: Name, in: Int, out: Int):
    def apply(args: List[Expr], res: List[Var]): Call =
      Error.report("wrong number of arguments or results in call", name, args, res):
        require(args.length == in && res.length == out)
      Call(name, args, res)

    def unapply(prog: Prog): Option[Call] =
      prog match
        case call @ Call(`name`, args, res) if args.length == in && res.length == out =>
          Some(call)

        case _ =>
          None

  class unary(val fun: Fun) extends (Expr => Expr):
    def apply(arg: Expr): Expr =
      App(fun, List(arg))

    def unapply(expr: Expr) =
      expr match
        case App(`fun`, _, _, List(arg)) =>
          Some(arg)

        case _ =>
          None

  class binary(val fun: Fun) extends ((Expr, Expr) => Expr):
    def apply(arg1: Expr, arg2: Expr): Expr =
      App(fun, List(arg1, arg2))

    def unapply(expr: Expr) =
      expr match
        case App(`fun`, _, _, List(arg1, arg2)) =>
          Some((arg1, arg2))

        case _ =>
          None

  class ternary(val fun: Fun) extends ((Expr, Expr, Expr) => Expr):
    def apply(arg1: Expr, arg2: Expr, arg3: Expr): Expr =
      App(fun, List(arg1, arg2, arg3))

    def unapply(expr: Expr) =
      expr match
        case App(`fun`, _, _, List(arg1, arg2, arg3)) =>
          Some((arg1, arg2, arg3))

        case _ =>
          None

  class associative(fun: Fun, val assoc: Assoc) extends binary(fun):
    // there is no neutral element, unlike for commutative operators
    def apply(args: List[Expr]): Expr =
      Error.report("no arguments", fun.name):
        require(args.nonEmpty)
      assoc.reduce(args, this)

    def flatten(expr: Expr): List[Expr] =
      expr match
        case App(`fun`, _, _, List(arg1, arg2)) if assoc == Assoc.Left =>
          flatten(arg1) ++ List(arg2)

        case App(`fun`, _, _, List(arg1, arg2)) if assoc == Assoc.Right =>
          List(arg1) ++ flatten(arg2)

        case _ =>
          List(expr)

  // Note: unapply flattens nested applications
  class commutative(val fun: Fun, val neutral: Expr, val assoc: Assoc) extends (List[Expr] => Expr):
    def apply(arg1: Expr, arg2: Expr): Expr =
      App(fun, List(arg1, arg2))

    def apply(args: List[Expr]): Expr =
      args match
        case Nil       => neutral
        case List(arg) => arg
        case _         => assoc.reduce(args, apply)

    def flatten(exprs: List[Expr]): List[Expr] =
      exprs flatMap flatten

    def flatten(expr: Expr): List[Expr] =
      expr match
        case App(`fun`, _, _, args) =>
          flatten(args)

        case _ =>
          List(expr)

    // additionally drops occurrences of the neutral element
    def flattenStrong(expr: Expr): List[Expr] =
      expr match
        case App(`fun`, _, _, args) =>
          args flatMap flattenStrong

        case `neutral` =>
          Nil

        case _ =>
          List(expr)

    def unapply(expr: Expr) =
      expr match
        case App(`fun`, _, _, args) =>
          Some(flatten(args))

        case _ =>
          None
