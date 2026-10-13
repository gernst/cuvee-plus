package cuvee.prove

import cuvee.Config
import cuvee.Error
import cuvee.sexpr
import cuvee.pipe.Transform
import cuvee.core._

// the deduction engine of -prove (see doc/prove.md and ideas/deduction-engine-implementation.md): the assertions and
// lemmas with the attribute :rw so far are rewrite rules and those with :fw forward lemmas (see Forward), which are
// kept as they are, the goals and the other
// assertions are simplified under a context of congruence classes and linear constraints with these rules (see
// Simplify, Rewrite, Context), each with a fresh number of rewrite steps; goals that simplify to true are dropped;
// like -simplify, with -rules the rules applied follow each assertion as (set-info :used ((name count) ...))
object Prove extends Transform:
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val rules = Rules.from(state, prefix ++ cmds)
    val forward = Forward.from(prefix ++ cmds)

    def fresh() = Context.empty(state).withRules(rules).copy(forward = forward)

    for
      cmd <- cmds
      ctx = fresh()
      cmd_ <- if cmd.isRule || Forward.is(cmd) then List(cmd) else cases(config, state, fresh, Simplify.simplify(config, state, ctx, cmd), 4) :: used(config, ctx, cmd)
      if !isTrivial(cmd_)
    yield cmd_

  // a goal that remains is proved by cases on the first premise that is a disjunction of at most three formulas, each
  // case with a context of its own, at most `depth` premises deep, e.g. n == zero || integer(n) < 1 that the rules of
  // mods introduce (in-de41); it is kept as it is unless all cases hold, so that the output does not multiply
  def cases(config: Config, state: State, fresh: () => Context, cmd: Cmd, depth: Int): Cmd =
    cmd match
      case Assert(justify, params, phi, attrs) if depth > 0 =>
        alternatives(phi) match
          case Some(phis) if phis.forall(phi_ => isTrivial(cases(config, state, fresh, Simplify.simplify(config, state, fresh(), Assert(justify, params, phi_, attrs)), depth - 1))) =>
            Assert(justify, params, True, attrs)

          case _ =>
            cmd

      case _ =>
        cmd

  // the goals for the cases of the first disjunctive premise of forall xs. φ₁ && ... && φₙ ==> ψ
  def alternatives(phi: Expr): Option[List[Expr]] =
    phi match
      case All(xs, body) =>
        alternatives(body).map(_.map(All(xs, _)))

      case Imp(ante, concl) =>
        val premises = And.flatten(ante)
        premises.indexWhere(premise => Or.flatten(premise).length.min(4) match { case 2 | 3 => true; case _ => false }) match
          case -1 =>
            None

          case i =>
            Some(for disjunct <- Or.flatten(premises(i)) yield Imp(And(premises.patch(i, List(disjunct), 1)), concl))

      case _ =>
        None

  def used(config: Config, ctx: Context, cmd: Cmd): List[Cmd] =
    cmd match
      case _: Assert if config.rules =>
        val counts = ctx.applied.value.toList.groupMapReduce(_._1)(_._2)(_ + _).toList.sorted
        if counts.isEmpty then Nil
        else List(SetInfo("used", counts.map((name, n) => List(sexpr.Id(name), sexpr.Num(n.toString)))))

      case _ =>
        Nil

  def isTrivial(cmd: Cmd) =
    cmd match
      case Assert(_, _, True, _) => true
      case _                     => false
