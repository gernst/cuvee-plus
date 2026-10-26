package cuvee.prove

import cuvee.core._

// a sequent at the current position of the engine (see doc/prove.md)
//
// state: the declarations, e.g. the datatypes whose selectors read the components of traces (see Views)
//
// bound: the variables bound by enclosing binders, one list per binder, innermost first;
// the variables of one binder are not nested, e.g. in forall x, y. phi, y is not in the scope of x (see Simplify.point)
//
// universal, existential: those of the bound variables that are quantified universally and existentially,
// seen from the current position, i.e., swapped below negations and premises (see flip);
// the equations x == e of the existential ones are true (one-point rule, see Simplify.point)
//
// facts: the assumptions, known to hold, and the conclusions, known not to hold (see Facts)
//
// classes: the congruence closure over the terms of the facts (see Classes), in place of the chains of variable
// equations of the simplifier: the definitions of a variable are the members of its class
//
// linear: the linear constraints on Int and Real among the facts, decided by the simplex (see Linear)
//
// polarity: Some(true) if the current position occurs positively, Some(false) if it occurs negatively,
// and None if it occurs in both ways or not in a formula
//
// rules, steps: the rewrite rules, which are applied after each round of simplification, and the remaining number
// of steps
//
// self: within the update of a combinator that defines a dependency, X == trace(...) or Y == maps(...), that
// dependency and its value in the update, whose invariants the update assumes (see Simplify.invariants): ⌊X⌋ and the
// accumulator, each history ⌊S⌋.j and its accumulator for a trace of several, and the history of the own component
// and the accumulator of a projection (see Views.selfOf and Views.relation)
//
// applied: the number of applications of each rule by its name, for -rules
//
// active: the rules whose side conditions are being evaluated at this position and the components of traces of several accumulators
// whose views are being computed (see Rewrite.apply and Views.projected), which are not applied or projected inside;
// one facility for both kinds of re-entrance, by identity for rules and by the key of a component for views
//
// memos: the memos of the engine (see Context.Memos), shared by the copies of this context like steps and fresh for
// each command (see withRules)
//
// forward: the forward lemmas, whose instances at the terms of the facts that the traversal assumes are assumed with
// them (see Forward.assume), none while a trigger is matched
case class Context(
    state: State,
    bound: List[List[Var]],
    universal: Set[Var],
    existential: Set[Var],
    facts: Facts,
    classes: Classes,
    linear: Linear,
    polarity: Option[Boolean],
    rules: List[Rule] = Nil,
    steps: util.Ref[Int] = util.Ref(0),
    self: List[(Expr, Expr)] = Nil,
    applied: util.Ref[Map[String, Int]] = util.Ref(Map()),
    active: List[AnyRef] = Nil,
    memos: util.Ref[Context.Memos] = util.Ref(Context.Memos()),
    forward: List[Forward] = Nil
):
  // the rewrite rules with a fresh number of steps and no memos, which are shared by the copies of this context, and
  // which guards against rules that do not terminate
  def withRules(rules: List[Rule], steps: Int = 1000) =
    copy(rules = rules, steps = util.Ref(steps), applied = util.Ref(Map()), memos = util.Ref(Context.Memos()))

  // an expression seen through its class, never a variable: a variable matches only by a definition that is not a
  // variable, the first member of its class that is none, any other expression as itself,
  // e.g. ctx.↑(Counter(i, c, n)) matches a variable K with K == counter(i, c, n) among the assumptions
  object ↑ :
    def unapply(expr: Expr): Option[Expr] =
      expr match
        case x: Var => defs(x).headOption
        case _      => Some(expr)

  // the definitions of a variable, which the matcher tries after the variable itself: the members of its class that
  // are not variables and do not contain it (see Rewrite.matchesExpr); only variables have definitions, as in the
  // simplifier: a term matched by a term of its class that contains it, e.g. a[k] by S.2[k] == a[k] assumed from a
  // sibling conjunct, is rewritten to a term that contains a[k] again, without end; containment modulo the classes,
  // e.g. through a variable equal to it, is left to the rewrite, which rejects a result that contains its term modulo
  // the classes (see Classes.within, examples/svlib/verify/teq_definitions_class.svlib)
  def defs(expr: Expr): List[Expr] =
    expr match
      case x: Var => classes.defs(x).filterNot(_.free.contains(x))
      case _      => Nil

  // whether `rule` is suspended at this position, by identity
  def suspended(rule: Rule): Boolean =
    active.exists(_ eq rule)

  // whether the component `key` of a trace is being projected at this position (see Views.projected)
  def projecting(key: AnyRef): Boolean =
    active.exists(_ == key)

  // the context with the facts that `keep` selects only, e.g. those that mention the variables of a view (see
  // Views.projected), with the same bound variables, rules of the input, and memos; the rules of the facts of the
  // context are dropped (they have no name, see Context.rules) and come back with the facts that are kept
  def restricted(keep: Expr => Boolean): Context =
    val base = copy(facts = Facts.empty, classes = Classes.empty(state.constrs.values.toSet), linear = Linear.empty, rules = rules.filter(_.name.isDefined))
    base.assume(facts.assms.filter(keep), facts.concls.filter(keep))

  // variables bound by let, match, and the combinators, which are neither universal nor existential
  def bind(xs: List[Var]) =
    copy(bound = xs :: bound)

  def forall(xs: List[Var]) =
    copy(bound = xs :: bound, universal = universal ++ xs)

  def exists(xs: List[Var]) =
    copy(bound = xs :: bound, existential = existential ++ xs)

  // the depth of the scope that binds x and its position there, (0, 0) for the free variables
  def scope(x: Var): (Int, Int) =
    val i = bound.indexWhere(_ contains x)
    if i < 0 then (0, 0) else (bound.length - i, bound(i).indexOf(x))

  // the order of the roots of the classes, by the scopes of this context (see Classes.Order)
  given order: Classes.Order = Classes.Order(Classes.rank(scope))

  // below a negation or in the premise of an implication, where universal variables become existential
  // and vice versa, since forall x. !phi is !exists x. !!phi
  def flip =
    copy(universal = existential, existential = universal, polarity = polarity.map(!_))

  // in a position without polarity, also below positions whose siblings are not recorded in the context,
  // e.g. the other branch of ite, where the one-point rule must not apply
  def neutral =
    copy(universal = Set(), existential = Set(), polarity = None)

  // variables that occur in the context
  def free: Set[Var] =
    bound.flatten.toSet ++ used

  // the facts known to hold as given, the assumptions and the negations of the conclusions (see Context.not);
  // side conditions of rules are matched against them (see Rewrite.conditions)
  def known: List[Expr] =
    facts.assms ++ facts.concls.map(Context.not)

  // variables that occur in the facts of the context, also those of the equations kept in the classes only
  def used: Set[Var] =
    facts.free ++ classes.free

  // each fact is passed to all theories: the classes and the linear constraints get it as given, such that the
  // matcher sees all its terms as members of their classes, the facts in canonical form (see Classes.normalize), all
  // of them again after a merge of classes, such that e.g. Simplify.implied finds (p y) for the fact (p x) with
  // x == y
  def assume(phi: Expr): Context =
    phi match
      case Eq(e1, e2) if e1 == e2 =>
        this

      case _ =>
        val phi_ = classes.normalize(phi)
        val classes_ = classes.assume(phi)
        val facts_ = if phi_ == True then facts else facts.assume(phi_)
        copy(facts = Context.renormalize(classes, classes_, facts_), classes = classes_, linear = linear.assume(phi), rules = Context.rules(phi) ++ rules).fix(phi)

  def deny(phi: Expr): Context =
    val classes_ = classes.deny(phi)
    val facts_ = facts.deny(phi)
    copy(facts = Context.renormalize(classes, classes_, facts_), classes = classes_, linear = linear.deny(phi)).fix(phi)

  // the variables of `phi` that the linear constraints fix to a value, e.g. k of 0 <= k and k < n with n <= 1, are
  // that value in the classes, which the simplex does not tell them, so that terms over them are decided, also
  // nonlinear ones; only after a fact that is a constraint, and only those not fixed already
  def fix(phi: Expr): Context =
    // fixed already: the class has a literal, which is a member, not the root, since variables are roots before
    // literals (see Classes.rank)
    val xs = phi.free.toList.filter(x => x.typ == Sort.int && !classes.classOf(x).exists(_.isInstanceOf[Lit]))
    if xs.isEmpty || linear.constraints.isEmpty
    then this
    else linear.fixed(xs).foldLeft(this) { case (ctx, (x, n)) => ctx.assume(Eq(x, Lit(n, Sort.int))) }

  def theories: List[Theory] =
    List(facts, classes, linear)

  def inconsistent =
    theories exists (_.inconsistent)

  // phi follows from a consistent context if denying it or assuming its negation makes one of the theories inconsistent,
  // where the negation is in normal form (see Context.not); an equation on Int or Real follows from both comparisons
  def implied(phi: Expr): Boolean =
    phi match
      case Eq(left, right) if Ring(left.typ).isDefined =>
        val le = if left.typ == Sort.int then Ints.le else Reals.le
        implied(le(left, right)) && implied(le(right, left))

      case _ =>
        !inconsistent && (deny(phi).inconsistent || assume(Context.not(phi)).inconsistent)

  // phi fails in a consistent context if assuming it or denying its negation makes one of the theories inconsistent
  def denied(phi: Expr): Boolean =
    !inconsistent && (assume(phi).inconsistent || deny(Context.not(phi)).inconsistent)

  // add facts known to hold (pos) and known not to hold (neg),
  // which are split along the boolean connectives into assumptions and conclusions
  def assume(pos: List[Expr], neg: List[Expr]): Context =
    (pos, neg) match
      case (Nil, Nil) =>
        this

      case (True :: pos, neg) =>
        assume(pos, neg)

      case (Not(phi) :: pos, neg) =>
        assume(pos, phi :: neg)

      case (And(phis) :: pos, neg) =>
        assume(phis ++ pos, neg)

      case (phi :: pos, neg) =>
        assume(phi).assume(pos, neg)

      case (Nil, False :: neg) =>
        assume(Nil, neg)

      case (Nil, Not(phi) :: neg) =>
        assume(List(phi), neg)

      case (Nil, Or(phis) :: neg) =>
        assume(Nil, phis ++ neg)

      case (Nil, Imp(phi, psi) :: neg) =>
        assume(List(phi), psi :: neg)

      case (Nil, phi :: neg) =>
        deny(phi).assume(Nil, neg)

object Context:
  // the facts after `classes` became `classes_`: those that mention a root that a merge or a solution changed, the
  // others are canonical already (see Classes.retired)
  def renormalize(classes: Classes, classes_ : Classes, facts: Facts): Facts =
    if classes_.merges == classes.merges
    then facts
    else facts.mapMentioning(classes_.retired.take(classes_.retired.length - classes.retired.length).toSet, classes_.normalize)

  // an equation of a term with variables and a ground term is a rewrite rule without instantiable variables,
  // whose free variables are constants; it terminates, since each step removes occurrences of variables
  def rules(phi: Expr): List[Rule] =
    phi match
      case Eq(lhs, rhs) if rule(lhs, rhs) => List(Rule(Set(), Set(), lhs, rhs, True))
      case Eq(rhs, lhs) if rule(lhs, rhs) => List(Rule(Set(), Set(), lhs, rhs, True))
      case _                              => Nil

  // whether lhs == rhs is a rule of the context: rhs is ground and lhs is not;
  // equations of variables are classes, those of arithmetic are normalized instead
  def rule(lhs: Expr, rhs: Expr): Boolean =
    !lhs.isInstanceOf[Var] && !lhs.isArith && lhs.free.nonEmpty && rhs.free.isEmpty

  // the negation in normal form, independent of a context: double negations are removed, and negated comparisons
  // are the other comparison with the arguments swapped, !(a < b) is b <= a
  def not(phi: Expr): Expr =
    phi match
      case True           => False
      case False          => True
      case Not(psi)       => psi
      case Ints.lt(a, b)  => Ints.le(b, a)
      case Ints.le(a, b)  => Ints.lt(b, a)
      case Reals.lt(a, b) => Reals.le(b, a)
      case Reals.le(a, b) => Reals.lt(b, a)
      case _              => Not(phi)

  // the memos of the engine, keyed by the canonical facts of the position (see Canon) and holding their values under
  // the canonical names: the facts of the contexts of the updates and bodies of combinators by their dependencies and
  // bound variables (see Simplify.combinator), the values of the bound variables of combinators, likewise (see
  // Simplify.iterations), the simplified views of the markers of traces of several accumulators (see Views), and the
  // canonical forms of the closed conditions with the renaming to them (see Canon)
  case class Memos(
      combinators: Map[(List[Expr], List[Var], Canon.Key), List[Expr]] = Map(),
      reads: Map[(List[Expr], List[Var], Canon.Key), List[Expr]] = Map(),
      views: Map[(Expr, Canon.Key), Expr] = Map(),
      canon: Map[(Expr, Subst[Nothing, Var]), Expr] = Map()
  )

  def empty(state: State) =
    Context(state, Nil, Set(), Set(), Facts.empty, Classes.empty(state.constrs.values.toSet), Linear.empty, None)
