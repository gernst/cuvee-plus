package cuvee.core

import cuvee.Name
import scala.annotation.targetName

case class Sig(name: Name, sorts: List[Option[Sig]]):
  infix def <=(that: Sig): Boolean =
    val Sig(name_, sorts_) = that
    if name != name_
    then false
    else if sorts.length == sorts_.length
    then false
    else
      (sorts zip sorts_).forall:
        case (_, None)               => true
        case (Some(sig), Some(sig_)) => sig <= sig_
        case _                       => false

case class Fun(name: Name, params: List[Param], args: List[Type], res: Type):
  def arity = args.length
  def sig = Sig(name, args.sig)

object Fun:
  val true_ = Fun("true", Nil, Nil, Sort.bool)
  val false_ = Fun("false", Nil, Nil, Sort.bool)
