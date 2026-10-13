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

  // the state trace, the key of the component (see key), the projection, and the view of a marker
  def view(config: Config, state: State, ctx: Context, expr: Expr): Option[(Expr, Key, Expr, Expr)] =
    expr match
      case App(sel, _, typ, List(arg)) =>
        for
          (constr, i) <- selector(state, sel)
          (tr, tr_, e) <- arg match
            case Current(tr @ ctx.↑(Trace(init, deps, acc, bound, update))) if constructed(constr, update) =>
              val tr_ = project(state, sel, typ, constr, i, tr, init, deps, acc, bound, update)
              Some((tr, tr_, Current(tr_)))

            case ctx.↑(Earlier(j, Butlast(tr @ ctx.↑(Trace(init, deps, acc, bound, update))))) if constructed(constr, update) =>
              val tr_ = project(state, sel, typ, constr, i, tr, init, deps, acc, bound, update)
              Some((tr, tr_, Earlier(j, Butlast(tr_))))

            case _ =>
              None
        yield (tr, key(sel, tr), tr_, e)

      case Maps(deps, bound, App(sel, _, typ, List(y: Var))) if bound.contains(y) =>
        for
          (constr, i) <- selector(state, sel)
          (tr, tr_, e) <- deps(bound.indexOf(y)) match
            case Butlast(tr @ ctx.↑(Trace(init, deps_, acc, bound_, update))) if constructed(constr, update) =>
              val tr_ = project(state, sel, typ, constr, i, tr, init, deps_, acc, bound_, update)
              Some((tr, tr_, Butlast(tr_)))

            case _ =>
              None
        yield (tr, key(sel, tr), tr_, e)

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
  // memoized per command by the marker, the bound variables and the classes (not the full context: a view computed
  // under weaker facts is reused, see ideas/state-trace-review.md)
  def projected(config: Config, state: State, ctx: Context, expr: Expr): Option[Expr] =
    for
      (_, key, _, e) <- view(config, state, ctx, expr)
      if !ctx.projecting(key)
    yield
      val memo = (expr, ctx.bound, ctx.classes)
      ctx.views.value.get(memo) match
        case Some(e_) =>
          e_

        case None =>
          val e_ = Simplify.simplify(config, state, ctx.neutral.copy(active = key :: ctx.active), e)
          Debug.step("rewrite", "view " + Simplify.show(config.output.printer, expr), Simplify.show(config.output.printer, e_))
          ctx.views := ctx.views.value + (memo -> e_)
          e_

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
