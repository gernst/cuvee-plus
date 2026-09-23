package cuvee.core

import scala.annotation.targetName
import cuvee.Name

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

extension (self: Iterable[Expr])
  @targetName("Exprs.free")
  def free = self.flatMap(_.free).toSet

  @targetName("Exprs.params")
  def params = self.flatMap(_.params).toSet

extension (self: Iterable[Prog])
  @targetName("Progs.mod")
  def mod = self.flatMap(_.mod).toSet

extension (self: List[Expr]) def types = self.map(_.typ)

class Quant(name: Name):
  def apply(bound: List[Var], body: Expr) =
    Bind(name, bound, body)

  def unapply(expr: Expr) =
    expr match
      case Bind(`name`, bound, body) =>
        Some((bound, body))

      case _ =>
        None

object Forall extends Quant("forall")
object Exists extends Quant("exists")
