package cuvee.transform

import cuvee.Config
import cuvee.sexpr
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.simplify.Normalize

// splitting of goals and lemmas into individual proof obligations of the form
// forall xs. antecedents ==> succedents, e.g. those from VCGen, which are reported separately by the solvers,
// as a sequent calculus (after the splitter of the earlier Cuvée, cuvee.pure.Horn):
// conclusions are decomposed into conjunctions, which are split, and disjunctions, whose disjuncts are succedents,
// negated conclusions and the premises of implications are antecedents, if-then-else is split by its test,
// the bound variables of universal quantifiers are moved into the context;
// antecedents are decomposed as well: conjunctions are flattened, negations are pushed inwards,
// existential quantifiers bind their variables in the context,
// and disjunctions and if-then-else are split into cases;
// obligations that are true, e.g. those with false among the antecedents
// or with a succedent that is also an antecedent, are dropped, as are duplicates;
// beforehand, if-then-else is lifted out of the terms of atoms (see Normalize.lift), such that it is split as well
object Split extends Transform:
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Option[Cmd]): (List[Cmd], Option[Cmd]) =
    val cmds_ =
      for
        cmd <- cmds
        cmd_ <- split(cmd)
      yield cmd_

    (cmds_, last)

  // rewrite rules are kept as they are, like in Simplify, since their pieces would be rules of their own
  def split(cmd: Cmd): List[Cmd] =
    cmd match
      case _ if cmd.isRule =>
        List(cmd)

      case Assert(justify, params, phi, attrs) =>
        split(Nil, Nil, Normalize.lift(phi)) match
          case List(phi_) =>
            List(Assert(justify, params, phi_, attrs))

          // the parts are named apart, since solvers reject a name that is already defined
          case phis =>
            for (phi_, i) <- phis.zipWithIndex
            yield Assert(justify, params, phi_, part(attrs, i + 1))

      case _ =>
        List(cmd)

  // the attributes of the `i`-th part of a split assertion, whose name, if any, gets the suffix `_i`
  def part(attrs: Attrs, i: Int): Attrs =
    val attrs_ =
      for (kw, arg) <- attrs.attrs
      yield arg match
        case Some(id: sexpr.Id) if kw == "named" => (kw, Some(sexpr.Id(id.text + "_" + i)))
        case _                                 => (kw, arg)

    Attrs(attrs_)

  // the obligations of `phi` under the bound variables and the antecedents of the context
  def split(bound: List[Var], ant: List[Expr], phi: Expr): List[Expr] =
    assert(List(phi), bound, ant, Nil).distinct

  // the obligations for the conclusions `todo` and the succedents `suc` so far,
  // under the bound variables and antecedents of the context, all in order
  def assert(todo: List[Expr], bound: List[Var], ant: List[Expr], suc: List[Expr]): List[Expr] =
    todo match
      case Nil =>
        obligation(bound, ant, suc)

      case True :: rest =>
        Nil

      case False :: rest =>
        assert(rest, bound, ant, suc)

      case Not(phi) :: rest =>
        assume(List(phi), rest, bound, ant, suc)

      case Imp(phi, psi) :: rest =>
        assume(List(phi), psi :: rest, bound, ant, suc)

      case Or(phis) :: rest =>
        assert(phis ++ rest, bound, ant, suc)

      case And(phis) :: rest =>
        phis.flatMap(phi => assert(phi :: rest, bound, ant, suc))

      case Ite(test, left, right) :: rest if left.typ == Sort.bool =>
        assume(List(test), left :: rest, bound, ant, suc) ++ assume(List(Not(test)), right :: rest, bound, ant, suc)

      case All(xs, body) :: rest =>
        val (xs_, body_) = avoid(bound, xs, body)
        assert(body_ :: rest, bound ++ xs_, ant, suc)

      case phi :: rest =>
        assert(rest, bound, ant, suc :+ phi)

  // the obligations with the additional antecedents `that`, which are decomposed first
  def assume(that: List[Expr], todo: List[Expr], bound: List[Var], ant: List[Expr], suc: List[Expr]): List[Expr] =
    that match
      case Nil =>
        assert(todo, bound, ant, suc)

      case True :: rest =>
        assume(rest, todo, bound, ant, suc)

      case False :: rest =>
        Nil

      case And(phis) :: rest =>
        assume(phis ++ rest, todo, bound, ant, suc)

      case Not(Not(phi)) :: rest =>
        assume(phi :: rest, todo, bound, ant, suc)

      case Not(Imp(phi, psi)) :: rest =>
        assume(phi :: Not(psi) :: rest, todo, bound, ant, suc)

      case Not(Or(phis)) :: rest =>
        assume(phis.map(Not(_)) ++ rest, todo, bound, ant, suc)

      case Not(Ex(xs, body)) :: rest =>
        assume(All(xs, Not(body)) :: rest, todo, bound, ant, suc)

      case Or(phis) :: rest =>
        phis.flatMap(phi => assume(phi :: rest, todo, bound, ant, suc))

      case Ite(test, left, right) :: rest if left.typ == Sort.bool =>
        assume(test :: left :: rest, todo, bound, ant, suc) ++ assume(Not(test) :: right :: rest, todo, bound, ant, suc)

      case Ex(xs, body) :: rest =>
        val (xs_, body_) = avoid(bound, xs, body)
        assume(body_ :: rest, todo, bound ++ xs_, ant, suc)

      case phi :: rest =>
        assume(rest, todo, bound, ant :+ phi, suc)

  // forall bound. ant ==> suc, where only the bound variables that occur are quantified,
  // true if a succedent is an antecedent
  def obligation(bound: List[Var], ant: List[Expr], suc: List[Expr]): List[Expr] =
    if suc.exists(ant.contains)
    then Nil
    else
      val ant_ = ant.distinct
      val suc_ = Or(suc.distinct)
      val phi = if ant_.isEmpty then suc_ else Imp(And(ant_), suc_)
      List(All(bound.filter(phi.free.contains), phi))

  // the bound variables `xs` renamed apart from those of the context
  def avoid(bound: List[Var], xs: List[Var], body: Expr): (List[Var], Expr) =
    val (xs_, su) = Subst.rename(xs, bound.toSet)
    (xs_, su(body))
