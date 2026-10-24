package cuvee.prove

import cuvee.core._

// normalization of formulas into clauses forall xs. antecedents ==> succedents, after the earlier Cuvée (cuvee.pure.Clause):
// conjunctions among the antecedents and disjunctions among the succedents are flattened, implications are split,
// negations that are not of atoms move to the other side, existential quantifiers among the antecedents and
// universal quantifiers among the succedents bind their variables in the prefix,
// let among the antecedents is exists xs. xs = args and body, and among the succedents forall xs. xs = args ==> body,
// such that its bindings are equations like any other;
// the antecedents are normalized as clauses themselves, the succedents as conjunctions exists ys. a and not s;
// unlike Split, the formula is not split into several obligations, it is equivalent to the result
object Normalize:
  def apply(phi: Expr): Expr =
    sequent(phi.free, phi)

  // atoms are not built by the logical connectives and quantifiers
  def isAtomic(phi: Expr): Boolean =
    phi match
      case True | False | And(_) | Or(_) | Imp(_, _) | Not(_) | Bind(_, _, _) | Let(_, _, _) => false
      case _                                                                                => true

  def isSimpleSequent(phi: Expr): Boolean =
    phi match
      case Not(psi) => isAtomic(psi)
      case _        => isAtomic(phi)

  // the clause of `phi`, true if it is trivial
  def sequent(bound: Set[Var], phi: Expr): Expr =
    if isSimpleSequent(phi)
    then phi
    else
      flatten(bound, Nil, List(phi)) match
        case None                 => True
        case Some((xs, ant, suc)) => clause(xs, ant, suc)

  // the conjunction exists xs. ant and not suc that `phi` holds, false if it is trivial
  def goal(bound: Set[Var], phi: Expr): Expr =
    if isAtomic(phi)
    then phi
    else
      flatten(bound, List(phi), Nil) match
        case None                 => False
        case Some((xs, ant, suc)) => Ex(xs, And(ant ++ suc.map(Not(_))))

  // a clause without succedents is the negation of its antecedents
  def clause(xs: List[Var], ant: List[Expr], suc: List[Expr]): Expr =
    if ant.isEmpty
    then All(xs, Or(suc))
    else if suc.isEmpty
    then All(xs, Not(And(ant)))
    else All(xs, Imp(And(ant), Or(suc)))

  // the clause forall xs. pos ==> neg as its bound variables, antecedents, and succedents, None if it is trivially true;
  // `bound` are the variables in scope, which the variables of the prefix are renamed apart from
  def flatten(bound: Set[Var], pos: List[Expr], neg: List[Expr]): Option[(List[Var], List[Expr], List[Expr])] =
    (pos, neg) match
      case (Nil, Nil)          => Some((Nil, Nil, Nil))
      case (False :: _, _)     => None
      case (_, True :: _)      => None

      case (True :: pos, neg)      => flatten(bound, pos, neg)
      case (And(phis) :: pos, neg) => flatten(bound, phis ++ pos, neg)

      case (pos, False :: neg)         => flatten(bound, pos, neg)
      case (pos, Imp(phi, psi) :: neg) => flatten(bound, pos :+ phi, psi :: neg)
      case (pos, Or(phis) :: neg)      => flatten(bound, pos, phis ++ neg)

      // negated atoms are kept among the antecedents
      case (Not(phi) :: pos, neg) if !isAtomic(phi) => flatten(bound, pos, phi :: neg)
      case (pos, Not(phi) :: neg)                   => flatten(bound, pos :+ phi, neg)

      // the bindings of let are equations, renamed apart from the variables of its arguments
      case (Let(xs, args, body) :: pos, neg) =>
        val (xs_, body_) = avoid(bound ++ args.free, xs, body)
        flatten(bound, Ex(xs_, And(Eq(xs_, args) :+ body_)) :: pos, neg)

      case (pos, Let(xs, args, body) :: neg) =>
        val (xs_, body_) = avoid(bound ++ args.free, xs, body)
        flatten(bound, pos, All(xs_, Imp(And(Eq(xs_, args)), body_)) :: neg)

      case (Ex(xs, phi) :: pos, neg) =>
        val (xs_, phi_) = avoid(bound, xs, phi)
        for (ys, ant, suc) <- flatten(bound ++ xs_, phi_ :: pos, neg)
        yield (xs_ ++ ys, ant, suc)

      case (pos, All(xs, phi) :: neg) =>
        val (xs_, phi_) = avoid(bound, xs, phi)
        for (ys, ant, suc) <- flatten(bound ++ xs_, pos, phi_ :: neg)
        yield (xs_ ++ ys, ant, suc)

      // other antecedents are normalized as clauses, which are flattened again if they change
      case (phi :: pos, neg) =>
        sequent(bound, phi) match
          case `phi` =>
            for (ys, ant, suc) <- flatten(bound, pos, neg)
            yield (ys, phi :: ant, suc)

          case phi_ =>
            flatten(bound, phi_ :: pos, neg)

      case (Nil, phi :: neg) =>
        goal(bound, phi) match
          case `phi` =>
            for (ys, ant, suc) <- flatten(bound, Nil, neg)
            yield (ys, ant, phi :: suc)

          case phi_ =>
            flatten(bound, Nil, phi_ :: neg)

  // ite is lifted out of the terms of the atoms to the level of formulas: A[ite(c, a, b)] is ite(c, A[a], A[b]),
  // where the connectives, quantifiers, and ite on formulas are traversed;
  // an ite below a binder of A is kept, since its test may refer to the bound variables,
  // and so is one below a derivative, which depends on the whole term, and below old, whose test refers to the old state
  def lift(phi: Expr): Expr =
    phi match
      case True | False         => phi
      case Not(psi)             => Not(lift(psi))
      case And(phis)            => And(phis.map(lift))
      case Or(phis)             => Or(phis.map(lift))
      case Imp(psi, chi)        => Imp(lift(psi), lift(chi))
      case Bind(quant, xs, psi) => Bind(quant, xs, lift(psi))
      case Let(xs, args, psi)   => Let(xs, args, lift(psi))

      case Ite(test, left, right) if phi.typ == Sort.bool =>
        Ite(lift(test), lift(left), lift(right))

      case _ =>
        ite(phi) match
          case Some(it @ Ite(test, left, right)) =>
            lift(Ite(test, replace(phi, it, left), replace(phi, it, right)))

          case _ =>
            phi

  // the outermost leftmost ite in `expr` that is not below a binder, a derivative, or old
  def ite(expr: Expr): Option[Expr] =
    expr match
      case Ite(_, _, _)       => Some(expr)
      case App(_, _, _, args) => args.view.flatMap(ite).headOption
      case Distinct(exprs)    => exprs.view.flatMap(ite).headOption
      case Is(arg, _)         => ite(arg)
      case As(arg, _)         => ite(arg)
      case _                  => None

  // the occurrences of `from` in `expr` that are not below a binder, a derivative, or old replaced by `to`
  def replace(expr: Expr, from: Expr, to: Expr): Expr =
    expr match
      case `from`                               => to
      case _: App | _: Distinct | _: Is | _: As => expr.map(replace(_, from, to))
      case _                                    => expr

  // the bound variables `xs` renamed apart from the variables in scope
  def avoid(bound: Set[Var], xs: List[Var], body: Expr): (List[Var], Expr) =
    val (xs_, su) = Subst.rename(xs, bound)
    (xs_, su(body))
