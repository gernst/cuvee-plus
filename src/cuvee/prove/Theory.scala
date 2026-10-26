package cuvee.prove

import cuvee.core._

// an immutable collection of facts of some theory, which records the facts it can express and ignores the others,
// and which detects when they contradict each other (see Context.assume)
trait Theory:
  def inconsistent: Boolean

object Facts:
  val empty = Facts(Nil, Nil, false)

// the facts as given, the assumptions are known to hold, the conclusions are known not to hold;
// they are inconsistent if false is among the assumptions, true among the conclusions, or a fact among both
case class Facts(assms: List[Expr], concls: List[Expr], inconsistent: Boolean) extends Theory:
  def assume(expr: Expr): Facts =
    val conflict = expr == False || (concls contains expr)
    Facts(expr :: assms, concls, inconsistent || conflict)

  def deny(expr: Expr): Facts =
    val conflict = expr == True || (assms contains expr)
    Facts(assms, expr :: concls, inconsistent || conflict)

  // a fact that is not recorded, e.g. an equation of variables kept in the classes, still conflicts with the conclusions
  def check(expr: Expr): Facts =
    val conflict = expr == False || (concls contains expr)
    Facts(assms, concls, inconsistent || conflict)

  def free: Set[Var] =
    assms.free ++ concls.free

  // the facts in the form f gives them, e.g. canonical after a merge of classes (see Context.assume), except those
  // that f decides, which are kept as they are: they are the facts that the classes record
  def map(f: Expr => Expr): Facts =
    def keep(phi: Expr) =
      f(phi) match
        case True | False => phi
        case phi_         => phi_
    Facts(assms.map(keep), concls.map(keep), inconsistent)
