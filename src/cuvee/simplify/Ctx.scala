package cuvee.simplify

import cuvee.core._

// a sequent at the current position of the simplifier:
// the assumptions are known to hold and the conclusions are known not to hold,
// together with the variables bound by enclosing binders
// and a substitution that replaces variables by others known to be equal
case class Ctx(bound: List[Var], assms: List[Expr], concls: List[Expr], su: Subst[Nothing, Var]):
  def bind(xs: List[Var]) =
    copy(bound = xs ++ bound)

  // equations between variables are recorded in the substitution
  def assume(phi: Expr): Ctx =
    phi match
      case Eq(e1, e2) if e1 == e2 =>
        this

      case Eq(x: Var, y: Var) if !(su.bound contains x) =>
        copy(su = su + (x -> y))

      case _ =>
        copy(assms = phi :: assms)

  def deny(phi: Expr) =
    copy(concls = phi :: concls)

  // add facts known to hold (pos) and known not to hold (neg),
  // which are split along the boolean connectives into assumptions and conclusions
  def assume(pos: List[Expr], neg: List[Expr]): Ctx =
    (pos, neg) match
      case (Nil, Nil) =>
        this

      case (True :: pos, neg) =>
        assume(pos, neg)

      case (Not(phi) :: pos, neg) =>
        assume(pos, phi :: neg)

      case (And(phis) :: pos, neg) =>
        assume(phis ++ pos, neg)

      case (phi :: pos, neg) =>
        assume(phi).assume(pos, neg)

      case (Nil, False :: neg) =>
        assume(Nil, neg)

      case (Nil, Not(phi) :: neg) =>
        assume(List(phi), neg)

      case (Nil, Or(phis) :: neg) =>
        assume(Nil, phis ++ neg)

      case (Nil, Imp(phi, psi) :: neg) =>
        assume(List(phi), psi :: neg)

      case (Nil, phi :: neg) =>
        deny(phi).assume(Nil, neg)

object Ctx:
  val empty = Ctx(Nil, Nil, Nil, Subst.empty)
