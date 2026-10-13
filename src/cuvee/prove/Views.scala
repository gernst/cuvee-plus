package cuvee.prove

import cuvee.Debug
import cuvee.Config
import cuvee.core._

// the per-variable traces of the paper as views of a trace with several accumulators (ideas/deduction-engine-plan.md,
// section 1.4): the reads of the components of such a trace S, current(S).i (Component), ⌊S⌋.i (History) and through
// it earlier(j, ⌊S⌋.i), are markers that stay in place; the matcher matches a marker modulo its view, the same read of
// the projection of S to the component (see project), simplified, such that the lemmas of the database meet the
// per-variable form; a marker is replaced by its view only once that reads no component of S any more (see closed)
//
// the projections do not unfold each other: the co-accumulators of a projection are bound variables over the
// histories ⌊S⌋.j, which are inert as dependencies (never rewritten in place), and a component is not projected inside
// its own view (Context.active, see projected)
object Views:
  // the trace of several accumulators that `expr` is or denotes (a variable defined by one, see Context.defs), as
  // referred to and as defined
  def traceOf(ctx: Context, expr: Expr): Option[(Expr, Trace)] =
    expr match
      case tr: Trace if tr.accs.length >= 2 => Some((tr, tr))
      case x: Var                           => ctx.defs(x).collectFirst { case tr: Trace if tr.accs.length >= 2 => (x, tr) }
      case _                                => None

  // the projection of the trace `tr`, referred to as `s`, to its component i: the trace of that accumulator alone from
  // its initial value with its result, the other accumulators bound over the histories of their components; the
  // dependencies that the result does not use are dropped by Simplify.trace, e.g. all histories for a counter
  def project(s: Expr, tr: Trace, i: Int): Trace =
    val Trace(inits, deps, accs, bound, results) = tr
    val others = accs.zipWithIndex.filter(_._2 != i)
    Trace(List(inits(i)), deps ++ others.map((_, j) => History(s, j)), List(accs(i)), bound ++ others.map(_._1), List(results(i)))

  // the projection of a marker as a term, for a pattern of the same shape (current of a trace, the history of a trace),
  // against which the matcher matches the pattern structurally without simplifying it (see Rewrite.matches); none for
  // patterns of other shapes, which need the normal form of the component (see projected)
  def structural(ctx: Context, pat: Expr, expr: Expr): Option[Expr] =
    (pat, expr) match
      case (Current(_: Trace), Component(s, i)) => traceOf(ctx, s).map((s_, tr) => Current(project(s_, tr, i)))
      case (Butlast(_: Trace), History(s, i))   => traceOf(ctx, s).map((s_, tr) => Butlast(project(s_, tr, i)))
      case _                                    => None

  // the trace referred to, the component, and the view of a marker
  def view(ctx: Context, expr: Expr): Option[(Expr, Int, Expr)] =
    expr match
      case Component(s, i) => traceOf(ctx, s).map((s_, tr) => (s_, i, Current(project(s_, tr, i))))
      case History(s, i)   => traceOf(ctx, s).map((s_, tr) => (s_, i, Butlast(project(s_, tr, i))))
      case _               => None

  // the component of a loop that is projected, by which it is suspended (see projected): the number of iterations of
  // the counter identifies the loop, since the trace term changes under simplification while its views are computed
  type Key = (Expr, Int)

  def key(tr: Trace, i: Int): Key =
    tr.deps match
      case Butlast(Counter(_, _, n)) :: _ => (n, i)
      case dep :: _                      => (dep, i)
      case Nil                           => (tr, i)

  // whether an expression reads no component of the trace `s`, i.e. has no marker of it
  def closed(s: Expr, expr: Expr): Boolean =
    expr match
      case Component(`s`, _) | History(`s`, _) => false
      case _ =>
        var yes = true
        expr.map { arg => yes = yes && closed(s, arg); arg }
        yes

  // the simplified view of a marker (see view), against which the matcher matches a pattern that does not match the
  // marker itself (see Rewrite.matches), like the definition of a variable (see Context.defs); the projection of a
  // component is not simplified again inside the simplification of its own view (e.g. the two arrays of a swap read
  // each other): the inner read stays a marker, which the rules treat as an opaque value, e.g. one stored into the
  // other array; the views are memoized per command by the marker and the relevant facts of the context under the
  // canonical names of its bound variables (see Canon), the facts that mention a variable of the view, under which
  // alone the view is simplified (see Context.restricted), such that reusing it at a position with the same relevant
  // facts is sound
  def projected(config: Config, state: State, ctx: Context, expr: Expr): Option[Expr] =
    for
      (s, i, e) <- view(ctx, expr)
      (_, tr) <- traceOf(ctx, s)
      key = this.key(tr, i)
      if !ctx.projecting(key)
    yield
      val relevant = e.free ++ e.free.flatMap(x => ctx.defs(x).flatMap(_.free))
      def keep(phi: Expr) = phi.free.nonEmpty && phi.free.subsetOf(relevant)
      val re = Canon.renaming(ctx.bound)
      val memo = (re(expr), Canon.key(ctx, re, keep))
      ctx.views.value.get(memo) match
        case Some(e_) =>
          Canon.back(re)(e_)

        case None =>
          Debug.info("views", "miss " + Simplify.show(config.output.printer, memo._1) + " with " + memo._2._2.size + " assumptions, " + memo._2._3.size + " conclusions")
          Debug.info("views", "  self " + memo._2._1.map((a, b) => Simplify.show(config.output.printer, a) + " ~ " + Simplify.show(config.output.printer, b)).mkString(", ") + " facts " + memo._2._2.map(Simplify.show(config.output.printer, _)).toList.sorted.mkString(" | "))
          val e_ = Simplify.simplify(config, state, ctx.restricted(keep).neutral.copy(active = key :: ctx.active), e)
          Debug.step("rewrite", "view " + Simplify.show(config.output.printer, expr), Simplify.show(config.output.printer, e_))
          ctx.views := ctx.views.value + (memo -> re(e_))
          e_

  // the self of a trace of several accumulators S, as defined by X == trace(...) (see Simplify.once): each history
  // ⌊S⌋.j denotes the accumulator j in the results, as ⌊X⌋ denotes the accumulator of a single trace
  def selfOf(s: Expr, accs: List[Var]): List[(Expr, Expr)] =
    if accs.length >= 2
    then accs.zipWithIndex.map((acc, j) => (History(s, j), acc))
    else List((Butlast(s), accs.head))

  // the self of a projection (see project) met by the traversal or the matcher, positionally: a single trace whose
  // dependencies are the histories ⌊S⌋.j of all components of some S but one, which its accumulator denotes; none
  // for other traces
  def relation(deps: List[Expr], acc: Var): List[(Expr, Expr)] =
    val histories = deps.collect { case History(s, j) => (s, j) }.groupMap(_._1)(_._2)
    val projections =
      for
        (s, js) <- histories.toList
        components = s.typ match
          case Sort(Con.trace, List(elem)) => Trace.components(elem)
          case _                           => Nil
        if js.length == components.length - 1
        missing <- (0 until components.length).find(i => !js.contains(i))
        if components(missing) == acc.typ
      yield (History(s, missing): Expr, acc: Expr)
    projections.take(1)
