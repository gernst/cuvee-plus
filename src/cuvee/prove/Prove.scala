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

    for
      cmd <- cmds
      ctx = Context.empty(state).withRules(rules).copy(forward = forward)
      cmd_ <- if cmd.isRule || Forward.is(cmd) then List(cmd) else Simplify.simplify(config, state, ctx, cmd) :: used(config, ctx, cmd)
      if !isTrivial(cmd_)
    yield cmd_

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
