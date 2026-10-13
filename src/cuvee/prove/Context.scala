package cuvee.prove

import cuvee.core._

// a sequent at the current position of the engine (after cuvee.simplify.Context, see doc/prove.md)
//
// state: the declarations, e.g. the datatypes whose selectors read the components of state traces (see Views)
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
// self: within the update of a combinator that defines a dependency, X == trace(...) or Y == maps(...),
// that dependency and its value in the update, whose invariants the update assumes (see Simplify.invariants); within
// the update of the projection of a state trace to a component, the read of that component, sel(s), and the
// accumulator of the projection, which denotes it (see Views.relation)
//
// projection: while the view of a component of a state trace is simplified or matched, the selector of the component
// (see Views.projected), from which the traversal and the matcher derive the self of each projection trace they meet
// (see Views.relation), positionally, since the bound variables of a trace are renamed on every round
//
// applied: the number of applications of each rule by its name, for -rules
//
// active: the rules whose side conditions are being evaluated at this position and the components of state traces
// whose views are being computed (see Rewrite.apply and Views.projected), which are not applied or projected inside;
// one facility for both kinds of re-entrance, by identity for rules and by the key of a component for views
//
// reads, views, combinators: the memos of the values of the bound variables of combinators (see Simplify.iterations),
// of the simplified views of the markers of state traces (see Views), and of the facts of the contexts of the updates
// and bodies of combinators (see Simplify.combinator), keyed by the canonical facts of the position (see Canon) and
// holding their values under the canonical names, shared by the copies of this context like steps and fresh for each
// command (see withRules)
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
    self: Option[(Expr, Expr)] = None,
    combinators: util.Ref[Context.Combinators] = util.Ref(Map()),
    applied: util.Ref[Map[String, Int]] = util.Ref(Map()),
    active: List[AnyRef] = Nil,
    reads: util.Ref[Context.Reads] = util.Ref(Map()),
    views: util.Ref[Context.Views] = util.Ref(Map()),
    canon: util.Ref[Map[(Expr, Subst[Nothing, Var]), Expr]] = util.Ref(Map()),
    projection: Option[Fun] = None
):
  // the rewrite rules with a fresh number of steps and no memoized contexts, views or reads, which are shared by the
  // copies of this context, and which guards against rules that do not terminate
  def withRules(rules: List[Rule], steps: Int = 1000) =
    copy(rules = rules, steps = util.Ref(steps), combinators = util.Ref(Map()), applied = util.Ref(Map()), reads = util.Ref(Map()), views = util.Ref(Map()), canon = util.Ref(Map()), linear = linear.copy(checks = util.Ref(Map())))

  // an expression seen through its class, never a variable: a variable matches only by a definition that is not a
  // variable, the first member of its class that is none, any other expression as itself,
  // e.g. ctx.↑(Counter(i, c, n)) matches a variable K with K == counter(i, c, n) among the assumptions
  object ↑ :
    def unapply(expr: Expr): Option[Expr] =
      expr match
        case x: Var => defs(x).headOption
        case _      => Some(expr)

  // the definitions of a variable, which the matcher tries after the variable itself: the members of its class that
  // are not variables and do not contain it (see Rewrite.matches); only variables have definitions, as in the
  // simplifier: a term matched by a term of its class that contains it, e.g. a[k] by S.2[k] == a[k] assumed from a
  // sibling conjunct, is rewritten to a term that contains a[k] again, without end
  def defs(expr: Expr): List[Expr] =
    expr match
      case x: Var => classes.defs(x).filterNot(_.free.contains(x))
      case _      => Nil

  // whether `rule` is suspended at this position, by identity
  def suspended(rule: Rule): Boolean =
    active.exists(_ eq rule)

  // whether the component `key` of a state trace is being projected at this position (see Views)
  def projecting(key: AnyRef): Boolean =
    active.exists(_ == key)

  // the context with the facts that `keep` selects only, e.g. those that mention the variables of a view (see
  // Views.projected), with the same bound variables, rules of the input, and memos; the rules of the facts of the
  // context are dropped (they have no name, see Context.rules) and come back with the facts that are kept
  def restricted(keep: Expr => Boolean): Context =
    val base = copy(facts = Facts.empty, classes = Classes.empty(state.constrs.values.toSet), linear = Linear.empty.copy(checks = linear.checks), rules = rules.filter(_.name.isDefined))
    base.assume(facts.assms.filter(keep), facts.concls.filter(keep))

  // variables bound by let, match, and the combinators, which are neither universal nor existential
  def bind(xs: List[Var]) =
    copy(bound = xs :: bound)

  def forall(xs: List[Var]) =
    copy(bound = xs :: bound, universal = universal ++ xs)

  def exists(xs: List[Var]) =
    copy(bound = xs :: bound, existential = existential ++ xs)

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

  // whether e does not depend on x through the definitions of the context, transitively, e.g. the solution of n by
  // an expression over a trace K with K == counter(0, 1, n), whose inlining would loop (see Simplify.poly)
  def acyclic(x: Var, e: Expr): Boolean =
    def reach(todo: List[Var], seen: Set[Var]): Set[Var] =
      todo match
        case Nil                         => seen
        case y :: rest if seen contains y => reach(rest, seen)
        case y :: rest =>
          val next = (linear.solved.get(y).toList ++ classes.classOf(y)).flatMap(_.free).toList
          reach(next ++ rest, seen + y)

    !reach(e.free.toList, Set()).contains(x)

  // each fact is passed to all theories, and stored as given, also the equations of variables, which the classes
  // substitute away (see Simplify.var_), such that the facts determine the classes and the linear constraints (the
  // memos are keyed by the facts, see Canon); facts are not normalized, e.g. Simplify.implied misses (p y) when the
  // fact is stored as (p x); this is done at the top level instead: Simplify.simplify iterates to a fixpoint
  def assume(phi: Expr): Context =
    phi match
      case Eq(e1, e2) if e1 == e2 =>
        this

      case _ =>
        copy(facts = facts.assume(phi), classes = classes.assume(phi), linear = linear.assume(phi), rules = Context.rules(phi) ++ rules)

  def deny(phi: Expr): Context =
    copy(facts = facts.deny(phi), classes = classes.deny(phi), linear = linear.deny(phi))

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

  // the facts of the contexts of combinators by their dependencies and bound variables and the key of the outer
  // context, all under the canonical names (see Canon)
  type Combinators = Map[(List[Expr], List[Var], Canon.Key), List[Expr]]

  // the values of the bound variables of combinators, likewise
  type Reads = Map[(List[Expr], List[Var], Canon.Key), List[Expr]]

  // the views of markers by the marker and the key of the context, likewise (see Views)
  type Views = Map[(Expr, Canon.Key), Expr]

  def empty(state: State) =
    Context(state, Nil, Set(), Set(), Facts.empty, Classes.empty(state.constrs.values.toSet), Linear.empty, None)
