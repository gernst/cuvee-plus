package cuvee.core

import scala.annotation.targetName

extension (self: List[Param])
  @targetName("Params.asIndex")
  def asIndex = self.map(_.asIndex)

extension (self: List[Var])
  def types = self.map(_.typ)
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
