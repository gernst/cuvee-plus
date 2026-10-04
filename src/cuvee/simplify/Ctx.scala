package cuvee.simplify

import cuvee.core._

// a sequent at the current position of the simplifier:
// the assumptions are known to hold and the conclusions are known not to hold,
// together with the variables bound by enclosing binders
// and a substitution that replaces variables by others known to be equal;
// the polarity of the current position is Some(true) if it occurs positively,
// Some(false) if it occurs negatively, and None if it occurs in both ways or not in a formula,
// e.g. below an equation or in the argument of a function;
// the context is inconsistent if it contains a contradiction,
// then the current position is irrelevant for the truth value of the whole formula;
// the rewrite rules are applied after each round of simplification (see Simplify.simplify)
case class Ctx(
    bound: List[Var],
    assms: List[Expr],
    concls: List[Expr],
    su: Subst[Nothing, Var],
    polarity: Option[Boolean],
    inconsistent: Boolean,
    rules: List[Rule] = Nil
):
  def withRules(rules: List[Rule]) =
    copy(rules = rules)

  def bind(xs: List[Var]) =
    copy(bound = xs ++ bound)

  // below a negation or in the premise of an implication
  def flip =
    copy(polarity = polarity.map(!_))

  // in a position without polarity
  def neutral =
    copy(polarity = None)

  // variables that occur in the context
  def free: Set[Var] =
    bound.toSet ++ assms.free ++ concls.free ++ su.bound ++ su.free

  // rename those of `xs` that clash with variables of the context (compared by name),
  // returning the fresh list of variables and the renaming to be applied to the scope of `xs`
  def avoid(xs: List[Var]): (List[Var], Subst[Nothing, Var]) =
    val names = free.map(_.name)
    val captured = xs.filter(x => names contains x.name)
    val re = Subst.from(captured, captured.fresh)
    (re.lhs(xs), re)

  // whether `phi` is known to hold (true) or known not to hold (false);
  // in an inconsistent context any formula may be chosen,
  // true at positive positions and false at negative positions
  def lookup(phi: Expr): Option[Boolean] =
    if inconsistent && phi.typ == Sort.bool && polarity.isDefined
    then polarity
    else if assms contains phi
    then Some(true)
    else if concls contains phi
    then Some(false)
    else None

  // equations between variables are recorded in the substitution;
  // facts are stored as given and not normalized under the substitution,
  // e.g. denying x = y when x is replaced by y is not detected as inconsistent here,
  // and lookup misses (p y) when the fact is stored as (p x);
  // this is done at the top level instead: Simplify.simplify iterates to a fixpoint,
  // where the facts are the simplified siblings, which are already rewritten under the substitution
  def assume(phi: Expr): Ctx =
    phi match
      case Eq(e1, e2) if e1 == e2 =>
        this

      case Eq(x: Var, y: Var) if !(su.bound contains x) =>
        copy(su = su + (x -> y))

      case _ =>
        val inconsistent_ = inconsistent || phi == False || (concls contains phi)
        copy(assms = phi :: assms, inconsistent = inconsistent_)

  def deny(phi: Expr): Ctx =
    val inconsistent_ = inconsistent || phi == True || (assms contains phi)
    copy(concls = phi :: concls, inconsistent = inconsistent_)

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
  val empty = Ctx(Nil, Nil, Nil, Subst.empty, None, false)

  // at the top of an asserted formula
  val pos = empty.copy(polarity = Some(true))
