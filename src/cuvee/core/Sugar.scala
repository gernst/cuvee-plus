package cuvee.core

import scala.annotation.targetName
import util.Name

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

extension (self: Iterable[Prog])
  @targetName("Progs.mod")
  def mod = self.flatMap(_.mod).toSet

extension (self: List[Type])
  @targetName("Types.sig")
  def sig = self.map(_.sig)

extension (self: List[Expr])
  @targetName("Exprs.types")
  def types = self.map(_.typ)

class Quant(name: Name):
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
    def apply(args: List[Expr]): Expr =
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
