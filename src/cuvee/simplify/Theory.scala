package cuvee.simplify

import cuvee.core._

// an immutable collection of facts of some theory, which records the facts it can express and ignores the others,
// and which detects when they contradict each other
trait Theory:
  def inconsistent: Boolean
  def assume(expr: Expr): Theory
  def deny(expr: Expr): Theory

object Facts:
  val empty = Facts(Nil, Nil)

// the facts as given, the assumptions are known to hold, the conclusions are known not to hold;
// they are inconsistent if false is among the assumptions or true among the conclusions
case class Facts(assms: List[Expr], concls: List[Expr]) extends Theory:
  def inconsistent =
    (assms contains False) || (concls contains True)

  def assume(expr: Expr): Facts =
    copy(assms = expr :: assms)

  def deny(expr: Expr): Facts =
    copy(concls = expr :: concls)

  // the variables that occur in the facts
  def free: Set[Var] =
    assms.free ++ concls.free
