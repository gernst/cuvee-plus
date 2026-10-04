package cuvee.transform

import cuvee.pipe.Transform
import cuvee.core._

// splitting of goals and lemmas into individual proof obligations of the form
// forall xs. antecedents ==> conclusion, e.g. those from Verify, which are reported separately by the solvers:
// conjunctions in the conclusion are split, the premises of implications and the bound variables of
// universal quantifiers are moved into the context, as well as negated existential quantifiers and disjunctions;
// obligations that are true are dropped
object Split extends Transform:
  def apply(config: cuvee.Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    for
      cmd <- cmds
      cmd_ <- split(cmd)
    yield cmd_

  def split(cmd: Cmd): List[Cmd] =
    cmd match
      case Assert(justify @ (Goal | Lemma), params, phi, attrs) =>
        for phi_ <- split(Nil, Nil, phi)
        yield Assert(justify, params, phi_, attrs)

      case _ =>
        List(cmd)

  // the obligations of `phi` under the bound variables and the antecedents (both in reverse) of the context,
  // the bound variables of quantifiers are renamed if they clash with those of the context
  def split(bound: List[Var], antecedents: List[Expr], phi: Expr): List[Expr] =
    phi match
      case True =>
        Nil

      case And(phis) =>
        phis.flatMap(split(bound, antecedents, _))

      // the conjuncts of the premise are antecedents of their own, trivial ones are dropped
      case Imp(premise, conclusion) =>
        split(bound, And.flattenStrong(premise).reverse ++ antecedents, conclusion)

      case All(xs, body) =>
        val (xs_, body_) = avoid(bound, xs, body)
        split(xs_.reverse ++ bound, antecedents, body_)

      case Not(Ex(xs, body)) =>
        val (xs_, body_) = avoid(bound, xs, body)
        split(xs_.reverse ++ bound, antecedents, Not(body_))

      case Not(Or(phis)) =>
        phis.flatMap(phi => split(bound, antecedents, Not(phi)))

      case _ =>
        val antecedents_ = antecedents.reverse
        val used = (phi.free ++ antecedents_.free)
        val bound_ = bound.reverse.filter(used.contains)
        List(All(bound_, if antecedents_.isEmpty then phi else Imp(And(antecedents_), phi)))

  def avoid(bound: List[Var], xs: List[Var], body: Expr): (List[Var], Expr) =
    val names = bound.map(_.name).toSet
    val clash = xs.filter(x => names.contains(x.name))

    if clash.isEmpty
    then (xs, body)
    else
      val su = Subst.from(clash, clash.fresh)
      (xs.map(x => su(x).asInstanceOf[Var]), su(body))
