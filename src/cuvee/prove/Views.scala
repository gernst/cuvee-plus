package cuvee.prove

import cuvee.Debug
import cuvee.Config
import cuvee.core._

// the per-variable traces of the paper as views of the state traces of -teq-state (see transform.StateTEQ and
// ideas/state-trace.md): the reads of the components of a state trace S, whose results are constructor applications,
// are markers that stay in place, a component of the current value, sel(current(S)), of an earlier value,
// sel(earlier(j, ⌊S⌋)), also through a bound variable s of a combinator over ⌊S⌋, which denotes the earlier value at
// its position (see Simplify.iterations), and the map of a component over ⌊S⌋; the matcher matches modulo these
// markers (see projected): the view of a marker is the same value of the projection of S to the component (see
// project), i.e. current(π(S)), earlier(j, ⌊π(S)⌋), and ⌊π(S)⌋, which is simplified before it is matched, such that
// the lemmas of the database meet the per-variable form; a marker is replaced by its view only once that reads no
// component any more (see Simplify.app and closed)
object Views:
  // the constructor whose selector `sel` is, and the position of the selector among its selectors, by the datatype of
  // the formal parameter of the selector, such that the lookup is cheap for the applications of other functions;
  // the tuples of the prelude of Dafny are datatypes like any other
  def selector(state: State, sel: Fun): Option[(Fun, Int)] =
    sel.formals match
      case List(Var(_, Sort(con, _))) =>
        state.datatypes.get(con.name).flatMap: data =>
          data.constrs.collectFirst:
            case (constr, sels) if sels.contains(sel) => (constr, sels.indexOf(sel))
      case _ =>
        None

  // the state trace, the selector of the component, the key of the component (see key), and the view of a marker
  def view(config: Config, state: State, ctx: Context, expr: Expr): Option[(Expr, Fun, Key, Expr)] =
    expr match
      case App(sel, _, typ, List(arg)) =>
        for
          (constr, i) <- selector(state, sel)
          (tr, e) <- arg match
            case Current(tr @ ctx.↑(Trace(init, deps, acc, bound, update))) if constructed(constr, update) =>
              Some((tr, Current(project(state, sel, typ, constr, i, tr, init, deps, acc, bound, update))))

            case ctx.↑(Earlier(j, Butlast(tr @ ctx.↑(Trace(init, deps, acc, bound, update))))) if constructed(constr, update) =>
              Some((tr, Earlier(j, Butlast(project(state, sel, typ, constr, i, tr, init, deps, acc, bound, update)))))

            case _ =>
              None
        yield (tr, sel, key(sel, tr), e)

      case Maps(deps, bound, App(sel, _, typ, List(y: Var))) if bound.contains(y) =>
        for
          (constr, i) <- selector(state, sel)
          (tr, e) <- deps(bound.indexOf(y)) match
            case Butlast(tr @ ctx.↑(Trace(init, deps_, acc, bound_, update))) if constructed(constr, update) =>
              Some((tr, Butlast(project(state, sel, typ, constr, i, tr, init, deps_, acc, bound_, update))))

            case _ =>
              None
        yield (tr, sel, key(sel, tr), e)

      case _ =>
        None

  // the component of a loop that is projected, by which it is suspended (see projected): the selector identifies the
  // component, the number of iterations of the counter the loop, since the trace term itself changes under
  // simplification while its views are computed, and a selector of a tuple is shared by all loops of that arity
  type Key = (Fun, Expr)

  def key(sel: Fun, tr: Expr): Key =
    tr match
      case Trace(_, Butlast(Counter(_, _, n)) :: _, _, _, _) => (sel, n)
      case Trace(_, dep :: _, _, _, _)                        => (sel, dep)
      case _                                                  => (sel, tr)

  // whether an expression reads no component of the state datatype of `constr`, i.e. has no marker of its selectors
  def closed(state: State, constr: Fun, expr: Expr): Boolean =
    val sels = state.datatypes.values.flatMap(_.constrs).collectFirst { case (`constr`, sels) => sels }.getOrElse(Nil)
    expr match
      case App(sel, _, _, _) if sels.contains(sel) => false
      case _ =>
        var yes = true
        expr.map { arg => yes = yes && closed(state, constr, arg); arg }
        yes

  // the simplified view of a marker (see view), against which the matcher matches a pattern that does not match the
  // marker itself (see Rewrite.matches), like the definition of a variable (see Context.defs); the projection of a
  // component is not simplified again inside the simplification of its own view, since the projections of components
  // that read each other would unfold each other without end (e.g. the two arrays of a swap): the inner read stays a
  // marker, which the rules then treat as an opaque value, e.g. one stored into the other array; the views are
  // memoized per command by the marker and the relevant facts of the context under the canonical names of its bound
  // variables (see Canon), such that positions that differ only by those names share them; the relevant facts are
  // those that mention a variable of the marker or of its view (the state trace, the counter, the constants of the
  // update), and the view is simplified under them only (see Context.restricted), such that reusing it at a position
  // with the same relevant facts is sound; the other facts of a position, e.g. the sibling conjuncts of the goal, made
  // the memos miss at nearly every position
  // the result is the view and the selector of the component, which the matcher sets as the projection of the context
  // in which it matches the view (see Rewrite.matches and relation)
  def projected(config: Config, state: State, ctx: Context, expr: Expr): Option[(Expr, Fun)] =
    for
      (_, sel, key, e) <- view(config, state, ctx, expr)
      if !ctx.projecting(key)
    yield
      // the variables of the view, not of the marker: the facts about the bound variable of the marker (the sibling
      // conjuncts of its position) vary by position and cannot reach the view, which reads the state by its position
      val relevant = e.free
      def keep(phi: Expr) = phi.free.intersect(relevant).nonEmpty
      val re = Canon.renaming(ctx.bound)
      val memo = (re(expr), Canon.key(ctx, re, keep))
      val e_ =
        ctx.views.value.get(memo) match
          case Some(e_) =>
            Canon.back(re)(e_)

          // the view is simplified with the selector as the projection of the context, from which the traversal derives
          // the relation of the projection trace: the read of the component from the accumulator s of the state trace is
          // the accumulator of the projection (see relation and Simplify.invariants)
          case None =>
            // -debug views reports the facts of a position whose view is computed, to see why memos miss
            Debug.info("views", "miss " + Simplify.show(config.output.printer, memo._1) + " with " + memo._2._2.size + " assumptions, " + memo._2._3.size + " conclusions: " + (memo._2._2 ++ memo._2._3).toList.map(_.hashCode.toHexString).sorted.mkString(" "))
            val e_ = Simplify.simplify(config, state, ctx.restricted(keep).neutral.copy(active = key :: ctx.active, projection = Some(sel)), e)
            Debug.step("rewrite", "view " + Simplify.show(config.output.printer, expr), Simplify.show(config.output.printer, e_))
            ctx.views := ctx.views.value + (memo -> re(e_))
            e_
      (e_, sel)

  // the relation of a projection trace (see project) to the component `sel` of the context's projection: the read of
  // the component from the bound variable of the state, the second one, and the accumulator, which denotes it; by
  // position, since the bound variables are renamed on every round; none for other traces, e.g. the state trace
  // itself or a counter, whose second bound variable is not of the state's type or whose component type differs
  def relation(state: State, ctx: Context, deps: List[Expr], acc: Var, bound: List[Var]): Option[(Expr, Expr)] =
    (ctx.projection, deps, bound) match
      case (Some(sel), _ :: Butlast(_) :: _, _ :: s :: _) if isState(state, sel, s.typ) && Type.expand(state, App(state, sel, List(s)).typ) == acc.typ =>
        Some((App(state, sel, List(s)), acc))
      case _ =>
        None

  // whether `typ` is the datatype whose selector `sel` is
  def isState(state: State, sel: Fun, typ: Type): Boolean =
    (sel.formals, typ) match
      case (List(Var(_, Sort(con, _))), Sort(con_, _)) => con == con_
      case _                                           => false

  // whether all results of an update are applications of `constr`
  def constructed(constr: Fun, update: Expr): Boolean =
    update match
      case Eps(updates)           => updates.forall(upd => constructed(constr, upd.rhs))
      case App(`constr`, _, _, _) => true
      case _                      => false

  // the projection of a state trace S == trace(s₀, for ⌊K⌋, Z do s, k, z :: constr(F₁(s), ..., Fₘ(s))) to its i-th
  // component: the trace of that component from its initial value, with the state trace among the dependencies
  // (⌊S⌋ bound to s) for the other components that the update reads, and its own component read from the accumulator;
  // the dependencies that the update does not use are dropped by Simplify.trace (e.g. ⌊S⌋ for a counter), after which
  // the lemmas of the database meet the per-variable form of the trace equation systems
  // `typ` is the type of the component, the result type of the selector instantiated for the state
  def project(state: State, sel: Fun, typ: Type, constr: Fun, i: Int, tr: Expr, init: Expr, deps: List[Expr], acc: Var, bound: List[Var], update: Expr): Expr =
    val x = Var("c", typ).fresh

    def comp(expr: Expr): Expr =
      expr match
        case Eps(updates)              => Eps(updates.map(upd => Upd(upd.cond, comp(upd.rhs))))
        case App(`constr`, _, _, args) => args(i)
        case _                         => App(state, sel, List(expr))

    def own(expr: Expr): Expr =
      expr match
        case App(`sel`, _, _, List(`acc`)) => x
        case _                             => expr.map(own)

    val init_ = comp(init)
    val update_ = own(comp(update))
    Trace(init_, deps.head :: Butlast(tr) :: deps.tail, x, bound.head :: acc :: bound.tail, update_)
