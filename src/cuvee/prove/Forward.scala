package cuvee.prove

import cuvee.Config
import cuvee.Debug
import cuvee.Error
import cuvee.sexpr
import cuvee.core._

// a forward lemma, the attribute :fw (package J of ideas/deduction-engine-plan.md): whenever a term that matches
// `trigger` occurs in a fact assumed by the traversal, the conclusion `concl` is assumed, instantiated by the match,
// if the condition `cond` holds; the trigger is a term of the conclusion, not a formula, since the conclusion is
// needed where only its term occurs, e.g. the bound current(incs(x0, b, ...)) <= b at the exit of the binary search,
// where the goal compares current(S).0 with other terms; variables of the condition only are bound against the
// facts of the context, as for rewrite rules (see Rewrite.conditions)
case class Forward(params: Set[Param], vars: Set[Var], trigger: Expr, concl: Expr, cond: Expr, attrs: Attrs):
  def name: Option[String] =
    attrs.values[sexpr.Id]("named").map(_.text).headOption

object Forward:
  // whether `cmd` is a forward lemma, kept as it is like the rules (see Prove)
  def is(cmd: Cmd): Boolean =
    cmd match
      case Assert(Axiom | Lemma, _, _, attrs) => attrs.contains("fw")
      case _                                  => false

  // the forward lemmas of the commands, in their order
  def from(cmds: List[Cmd]): List[Forward] =
    cmds.collect { case cmd @ Assert(_, params, phi, attrs) if is(cmd) =>
      Error.report("lemma with both :rw and :fw", phi):
        require(!attrs.contains("rw"))
      from(params.toSet, Set(), True, phi).copy(attrs = attrs)
    }

  // the universally quantified variables are those of the lemma, the premises its condition, as in Rule.from;
  // the lemma's variables in the conclusion must occur in the trigger or in the condition
  def from(params: Set[Param], vars: Set[Var], cond: Expr, phi: Expr): Forward =
    phi match
      case All(bound, body) =>
        from(params, vars ++ bound, cond, body)

      case Imp(cond_, body) =>
        from(params, vars, if cond == True then cond_ else And(cond, cond_), body)

      case _ =>
        val needed = phi.free intersect vars
        val candidates = terms(phi).filter(t => (needed -- t.free).subsetOf(cond.free))
        Error.report("forward lemma without a term that binds its variables", phi):
          require(candidates.nonEmpty)
        val trigger = candidates.maxBy(t => (t.free intersect vars).size)
        Forward(params, vars, trigger, phi, cond, Attrs.empty)

  // the boolean, comparison, and arithmetic structure of a formula, below which its terms are found
  val structure = Set("and", "or", "=>", "<=>", "not", "=", "distinct", "<", "<=", ">", ">=", "+", "-", "*")

  // the terms of a formula below its structure, outside binders: the maximal subterms that are no structure,
  // variables, or literals, and their subterms, in order and without duplicates; the terms at which triggers are tried
  def terms(phi: Expr): List[Expr] =
    def collect(expr: Expr): List[Expr] =
      expr match
        case _: Var | _: Lit | True | False =>
          Nil
        case App(fun, _, _, args) if structure.contains(fun.name.name) =>
          args.flatMap(collect)
        case _ if Canon.binds(expr) && !expr.isInstanceOf[App] =>
          List(expr)
        case _ =>
          var below: List[Expr] = Nil
          expr.map { arg => below = below ++ collect(arg); arg }
          expr :: below
    collect(phi).distinct

  // `expr` with the occurrences of `from` replaced by `to`
  def replace(expr: Expr, from: Expr, to: Expr): Expr =
    if expr == from then to else expr.map(replace(_, from, to))

  // the instances of `fw` at `term` in `ctx`: matched like the left-hand side of a rule (also by definitions and
  // views, see Rewrite.matches), the condition decided like that of a rule, and the trigger's instance replaced by the
  // term as it occurs, such that the fact is about the term of the goal, current(S).0 <= p, not about its view
  def fire(config: Config, state: State, ctx: Context, fw: Forward, term: Expr): List[Expr] =
    for
      _ <- Rewrite.matches(state, fw.params, fw.trigger.typ, term.typ, Subst.empty)
      subst <- Rewrite.matches(config, state, ctx, fw.params, fw.vars, Set(), fw.trigger, None, Map(), Set(), term, Subst.empty)
      subst_ <- Rewrite.conditions(config, state, ctx, fw.params, fw.vars, Set(), And.flatten(fw.cond), None, Map(), Set(), ctx.known, Rewrite.holds(config, state, ctx, _), subst)
    yield
      val phi = replace(subst_(fw.concl), subst_(fw.trigger), term)
      Debug.step("forward", fw.name.getOrElse("?") + " at " + Simplify.show(config.output.printer, term), Simplify.show(config.output.printer, phi))
      phi

  // the facts `pos` and `neg` assumed in `ctx` (see Context.assume), and the instances of the forward lemmas at their
  // terms; the instances are assumed by Context.assume, which fires no triggers, so they never fire again (generation
  // 1, which terminates), and while the triggers are matched and their conditions decided, no forward lemma fires
  // (the context of fire has none); an instance that is known already is skipped, so firing again after classes
  // merge changes nothing
  def assume(config: Config, state: State, ctx: Context, pos: List[Expr], neg: List[Expr]): Context =
    val ctx_ = ctx.assume(pos, neg)
    if ctx.forward.isEmpty || ctx_.inconsistent
    then ctx_
    else
      val inner = ctx_.copy(forward = Nil)
      val facts =
        for
          term <- (pos ++ neg).flatMap(terms).distinct
          fw <- ctx.forward
          phi <- fire(config, state, inner, fw, term)
        yield (fw, phi)
      // the instances assumed count as applications of their lemma, for -rules (see Context.applied)
      facts.distinct.foldLeft(ctx_) { case (ctx, (fw, phi)) =>
        if Rewrite.known(ctx, ctx.known, phi) || ctx.implied(phi)
        then ctx
        else
          for name <- fw.name
          do ctx.applied := ctx.applied.value.updated(name, ctx.applied.value.getOrElse(name, 0) + 1)
          ctx.assume(List(phi), Nil)
      }
