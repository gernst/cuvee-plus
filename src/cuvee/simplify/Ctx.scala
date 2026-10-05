package cuvee.simplify

import cuvee.core._

// a sequent at the current position of the simplifier:
// the assumptions are known to hold and the conclusions are known not to hold,
// together with the variables bound by enclosing binders
// a substitution that replaces variables by others or by literals known to be equal,
// and the equations x == e of the assumptions that are not recursive, i.e., where x is not free in e;
// `points` are the quantified variables whose equations x == e are true at the given polarity (one-point rule),
// which is only sound if the context records all siblings between the binder and the current position;
// the polarity of the current position is Some(true) if it occurs positively,
// Some(false) if it occurs negatively, and None if it occurs in both ways or not in a formula,
// e.g. below an equation or in the argument of a function;
// the context is inconsistent if false is among the assumptions or true among the conclusions,
// then the current position is irrelevant for the truth value of the whole formula;
// the rewrite rules are applied after each round of simplification (see Simplify.simplify)
case class Ctx(
    bound: List[Var],
    assms: List[Expr],
    concls: List[Expr],
    su: Map[Var, Expr],
    eq: Map[Var, Expr],
    polarity: Option[Boolean],
    points: Map[Var, Boolean] = Map(),
    rules: List[Rule] = Nil,
    steps: util.Ref[Int] = util.Ref(0)
):
  // the rewrite rules with a fresh number of steps, which is shared by the copies of this context,
  // and which guards against rules that do not terminate
  def withRules(rules: List[Rule], steps: Int = 1000) =
    copy(rules = rules, steps = util.Ref(steps))

  def bind(xs: List[Var]) =
    copy(bound = xs ++ bound)

  // the variables of a quantifier, whose equations are true at the opposite polarity for forall,
  // and at the same polarity for exists, which is undetermined at a position without polarity
  def quantify(quant: util.Name, xs: List[Var]) =
    val points_ =
      (quant.name, polarity) match
        case ("forall", Some(pol)) => xs.map(_ -> !pol)
        case ("exists", Some(pol)) => xs.map(_ -> pol)
        case _                     => Nil
    bind(xs).copy(points = points ++ points_)

  // below positions whose siblings are not recorded in the context, e.g. the other branch of ite
  def opaque =
    copy(points = Map())

  // below a negation or in the premise of an implication
  def flip =
    copy(polarity = polarity.map(!_))

  // in a position without polarity
  def neutral =
    copy(polarity = None, points = Map())

  // variables that occur in the context
  def free: Set[Var] =
    bound.toSet ++ used

  // variables that occur in the facts of the context, including the primed variables of derivatives,
  // which these refer to once the derivative is computed, but which are not free in Diff
  def used: Set[Var] =
    val facts = assms ++ concls
    facts.free ++ facts.flatMap(Ctx.primed) ++ su.keys ++ su.values.free ++ eq.keys ++ eq.values.free

  // rename those of `xs` that clash with variables of the context (compared by name),
  // returning the fresh list of variables and the renaming to be applied to the scope of `xs`
  def avoid(xs: List[Var]): (List[Var], Subst[Nothing, Var]) =
    val names = free.map(_.name)
    val captured = xs.filter(x => names contains x.name)
    val re = Subst.from(captured, captured.fresh)
    (re.lhs(xs), re)

  // equations of variables with variables and literals are recorded in the substitution;
  // facts are stored as given and not normalized under the substitution,
  // e.g. Simplify.implied misses (p y) when the fact is stored as (p x);
  // this is done at the top level instead: Simplify.simplify iterates to a fixpoint,
  // where the facts are the simplified siblings, which are already rewritten under the substitution
  def assume(state: State, phi: Expr): Ctx =
    phi match
      case Eq(e1, e2) if e1 == e2 =>
        this

      case Eq(x: Var, y: Var) if !(su contains x) =>
        copy(su = su + (x -> y))

      case Eq(x: Var, l: Lit) if !(su contains x) =>
        copy(su = su + (x -> l))

      case Eq(l: Lit, x: Var) if !(su contains x) =>
        copy(su = su + (x -> l))

      // the equation remains an assumption, such that it is still found by Simplify.implied;
      // equations whose right-hand side is a sum, difference, negation, or product are not recorded,
      // since rewriting follows the equations (see Rewrite.matches), whereas arithmetic is normalized instead
      case Eq(x: Var, e) if !(eq contains x) && !(e.free contains x) && !Ctx.arithmetic(e) =>
        copy(assms = phi :: assms, eq = eq + (x -> e))

      case Eq(e, x: Var) if !(eq contains x) && !(e.free contains x) && !Ctx.arithmetic(e) =>
        copy(assms = phi :: assms, eq = eq + (x -> e))

      case _ =>
        copy(assms = phi :: assms)

  def deny(phi: Expr): Ctx =
    copy(concls = phi :: concls)

  // false among the assumptions or true among the conclusions
  def inconsistent =
    (assms contains False) || (concls contains True)

  // add facts known to hold (pos) and known not to hold (neg),
  // which are split along the boolean connectives into assumptions and conclusions
  def assume(state: State, pos: List[Expr], neg: List[Expr]): Ctx =
    (pos, neg) match
      case (Nil, Nil) =>
        this

      case (True :: pos, neg) =>
        assume(state, pos, neg)

      case (Not(phi) :: pos, neg) =>
        assume(state, pos, phi :: neg)

      case (And(phis) :: pos, neg) =>
        assume(state, phis ++ pos, neg)

      case (phi :: pos, neg) =>
        assume(state, phi).assume(state, pos, neg)

      case (Nil, False :: neg) =>
        assume(state, Nil, neg)

      case (Nil, Not(phi) :: neg) =>
        assume(state, List(phi), neg)

      case (Nil, Or(phis) :: neg) =>
        assume(state, Nil, phis ++ neg)

      case (Nil, Imp(phi, psi) :: neg) =>
        assume(state, List(phi), psi :: neg)

      case (Nil, phi :: neg) =>
        deny(phi).assume(state, Nil, neg)

object Ctx:
  // applications of the basic arithmetic operators on Int or Real
  def arithmetic(expr: Expr): Boolean =
    Ring(expr.typ) match
      case Some(ring) =>
        expr match
          case ring.plus(_) | ring.minus(_, _) | ring.uminus(_) | ring.times(_) => true
          case _                                                                => false

      case None =>
        false

  // the primed variables x' of the derivatives (xs :: e)' in `expr`
  def primed(expr: Expr): Set[Var] =
    val inner = Set.newBuilder[Var]
    expr.map: arg =>
      inner ++= primed(arg)
      arg
    expr match
      case Diff(xs, _) => inner.result() ++ xs.map(_.primed)
      case _           => inner.result()

  val empty = Ctx(Nil, Nil, Nil, Map(), Map(), None)

  // at the top of an asserted formula
  val pos = empty.copy(polarity = Some(true))
