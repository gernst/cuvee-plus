package cuvee.prove

import util.Name
import cuvee.core._

// canonical keys for the memos of the engine (package B of ideas/deduction-engine-plan.md, in its restricted form):
// the bound variables of a context are renamed by their position, outermost binder first, such that two positions
// that differ only by the names of their bound variables (which the traversal renames apart from the context, see
// Subst.rename in Simplify) have the same canonical facts; the memos of the views, the reads and the combinator
// contexts are keyed by these and store their values under the canonical names, from which the names of the position
// are restored (see back); the traversal itself keeps its fresh names, nothing is renamed in place
object Canon:
  // the order of terms in canonical forms: by the (cached) hash first, by the printed form only on a collision, since
  // the ordering of Expr by its printed form costs a traversal
  given Ordering[Expr] = Ordering.by((e: Expr) => e.hashCode).orElseBy(_.toString)

  // the canonical names, which no input and no fresh variable has
  def canonical(i: Int, typ: Type): Var =
    Var(Name("§", Some(i)), typ)

  // the renaming of the bound variables of a context, and of `extra`, the variables bound next (e.g. those of a
  // combinator), which are numbered after them
  def renaming(bound: List[List[Var]], extra: List[Var] = Nil): Subst[Nothing, Var] =
    val xs = (bound.reverse.flatten ++ extra).distinct
    val ys = xs.zipWithIndex.map((x, i) => canonical(i, x.typ))
    Subst.from(xs, ys)

  // the inverse renaming, from the canonical names back to the variables of the position
  def back(re: Subst[Nothing, Var]): Subst[Nothing, Var] =
    Subst(Map(), re.vars.map(_.swap))

  // the canonical key of a context under the renaming of its bound variables: the dependency that it defines (see
  // Context.self) and its facts as sets, which determine its classes and linear constraints
  type Key = (Option[(Expr, Expr)], Set[Expr], Set[Expr])

  // the facts take their canonical form (see term), since their inner binders are renamed on every round of the
  // traversal; the canonical forms are cached per command by the fact and the renaming (see Context.canon)
  // `keep` selects the facts that the key comprises, e.g. those relevant to a view (see Views.projected)
  def key(ctx: Context, re: Subst[Nothing, Var], keep: Expr => Boolean = _ => true): Key =
    def canon(phi: Expr): Expr =
      val memo = (phi, re)
      ctx.canon.value.get(memo) match
        case Some(phi_) =>
          phi_
        case None =>
          val phi_ = term(re(phi))
          ctx.canon := ctx.canon.value + (memo -> phi_)
          phi_
    (ctx.self.map((dep, value) => (canon(dep), canon(value))), ctx.facts.assms.filter(keep).map(canon).toSet, ctx.facts.concls.filter(keep).map(canon).toSet)

  // the canonical form of a term, by which terms are compared modulo the names of their bound variables and the
  // orders that do not matter: the variables bound inside the term are renamed by their depth (the binders of one
  // scope take consecutive names, sibling scopes reuse them), the dependencies of a combinator are sorted with their
  // bound variables permuted along, the cases of a choice are sorted (their guards are disjoint), the arguments of
  // conjunctions and disjunctions are flattened and sorted, and the sides of an equation are sorted; the names of the
  // inner binders are apart from those of the renaming of a position (see canonical); for keys and comparisons only,
  // never for terms that are kept (see Rewrite.known, Simplify.eq_)
  def term(expr: Expr): Expr =
    term(expr, 0)

  def inner(i: Int, typ: Type): Var =
    Var(Name("¶", Some(i)), typ)

  // the renaming of the variables bound at `depth`, and the depth below them
  def scope(xs: List[Var], depth: Int): (Subst[Nothing, Var], Int) =
    (Subst.from(xs, xs.zipWithIndex.map((x, i) => inner(depth + i, x.typ))), depth + xs.length)

  def term(expr: Expr, depth: Int): Expr =
    expr match
      case Trace(inits, deps, accs, bound, results) =>
        val (deps_, bound_) = sorted(deps.map(term(_, depth)), bound)
        val (re, depth_) = scope(accs ++ bound_, depth)
        Trace(inits.map(term(_, depth)), deps_, accs.map(re(_)), bound_.map(re(_)), results.map(r => term(re(r), depth_)))

      case Maps(deps, bound, update) =>
        val (deps_, bound_) = sorted(deps.map(term(_, depth)), bound)
        val (re, depth_) = scope(bound_, depth)
        Maps(deps_, bound_.map(re(_)), term(re(update), depth_))

      case Invs(deps, bound, body) =>
        val (deps_, bound_) = sorted(deps.map(term(_, depth)), bound)
        val (re, depth_) = scope(bound_, depth)
        Invs(deps_, bound_.map(re(_)), term(re(body), depth_))

      case Bind(quant, bound, body) =>
        val (re, depth_) = scope(bound, depth)
        Bind(quant, bound.map(re(_)), term(re(body), depth_))

      case Lam(bound, body, typ) =>
        val (re, depth_) = scope(bound, depth)
        Lam(bound.map(re(_)), term(re(body), depth_), typ)

      case Let(bound, args, body) =>
        val (re, depth_) = scope(bound, depth)
        Let(bound.map(re(_)), args.map(term(_, depth)), term(re(body), depth_))

      case Eps(updates) =>
        Eps(updates.map(upd => Upd(term(upd.cond, depth), term(upd.rhs, depth))).sortBy(upd => (upd.cond, upd.rhs))(Ordering.Tuple2(summon[Ordering[Expr]], summon[Ordering[Expr]])))

      case And(phis) =>
        And(phis.map(term(_, depth)).sorted)

      case Or(phis) =>
        Or(phis.map(term(_, depth)).sorted)

      case Eq(left, right) =>
        val List(a, b) = List(term(left, depth), term(right, depth)).sorted: @unchecked
        Eq(a, b)

      // the patterns of cases bind their variables
      case Match(arg, cases) =>
        Match(term(arg, depth), cases.map(cs => cases_(cs, depth)))

      case Rec(fun, cases) =>
        Rec(fun, cases.map(cs => cases_(cs, depth)))

      case _ =>
        expr.map(term(_, depth))

  def cases_(cs: Case, depth: Int): Case =
    val Case(pat, body, cond) = cs
    val (re, depth_) = scope(pat.free.toList.sortBy(_.name.toString), depth)
    Case(re(pat), term(re(body), depth_), term(re(cond), depth_))

  // the dependencies in canonical order, with their bound variables permuted along
  def sorted(deps: List[Expr], bound: List[Var]): (List[Expr], List[Var]) =
    (deps zip bound).sortBy(_._1)(summon[Ordering[Expr]]).unzip

  // whether a term binds variables, i.e. has a canonical form that differs from itself
  def binds(expr: Expr): Boolean =
    expr match
      case _: Trace | _: Maps | _: Invs | _: Bind | _: Lam | _: Let | _: Match | _: Rec => true
      case _ =>
        var yes = false
        expr.map { arg => yes = yes || binds(arg); arg }
        yes

  // whether two terms are equal modulo their canonical forms, which is checked only if they bind variables, since
  // the canonical forms cost a traversal
  def equal(a: Expr, b: Expr): Boolean =
    a == b || (a.typ == b.typ && binds(a) && binds(b) && term(a) == term(b))
