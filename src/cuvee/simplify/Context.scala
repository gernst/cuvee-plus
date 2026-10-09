package cuvee.simplify

import cuvee.core._

// a sequent at the current position of the simplifier
//
// bound: the variables bound by enclosing binders, one list per binder, innermost first;
// the variables of one binder are not nested, e.g. in forall x, y. phi, y is not in the scope of x (see Simplify.point)
//
// universal, existential: those of the bound variables that are quantified universally and existentially,
// seen from the current position, i.e., swapped below negations and premises (see flip);
// the equations x == e of the existential ones are true (one-point rule, see Simplify.point),
// which is only sound if the context records all siblings between the binder and the current position
//
// facts: the assumptions, known to hold, and the conclusions, known not to hold (see Facts)
//
// chains: the equations of variables among the assumptions (see Chains)
//
// diffs: the difference constraints on Int among the facts (see Diffs)
//
// polarity: Some(true) if the current position occurs positively, Some(false) if it occurs negatively,
// and None if it occurs in both ways or not in a formula, e.g. below an equation or in the argument of a function;
// the context is inconsistent if one of its theories is,
// then the current position is irrelevant for the truth value of the whole formula
//
// rules, steps: the rewrite rules, which are applied after each round of simplification (see Simplify.simplify),
// and the remaining number of steps
//
// self: within the update of a combinator that defines a dependency, X == trace(...) or Y == maps(...),
// that dependency and its value in the update, whose invariants the update assumes (see Simplify.invariants)
//
// combinators: the contexts of the updates and bodies of combinators built so far (see Simplify.combinator),
// shared by the copies of this context like steps and fresh for each command (see withRules), such that the
// iterations of a combinator are not simplified again for each rule that is matched and in each round;
// the key comprises everything that the context depends on, in particular the facts, such that information
// that becomes available later yields a new context
case class Context(
    bound: List[List[Var]],
    universal: Set[Var],
    existential: Set[Var],
    facts: Facts,
    chains: Chains,
    diffs: Diffs,
    polarity: Option[Boolean],
    rules: List[Rule] = Nil,
    steps: util.Ref[Int] = util.Ref(0),
    self: Option[(Expr, Expr)] = None,
    combinators: util.Ref[Context.Combinators] = util.Ref(Map())
):
  // the rewrite rules with a fresh number of steps and no contexts of combinators yet, which are shared by the copies
  // of this context,
  // and which guards against rules that do not terminate
  def withRules(rules: List[Rule], steps: Int = 1000) =
    copy(rules = rules, steps = util.Ref(steps), combinators = util.Ref(Map()))

  // an expression seen through the equations of chains.chain, never a variable: a variable matches only by
  // a definition that is not a variable, any other expression as itself,
  // e.g. ctx.↑(Counter(i, c, n)) matches a variable K with K == counter(i, c, n) among the assumptions
  object ↑ :
    def unapply(expr: Expr): Option[Expr] =
      expr match
        case x: Var => chains.chain.get(x).filterNot(_.isInstanceOf[Var])
        case _      => Some(expr)

  // the parts of this context that determine the contexts of combinators built in it, besides the rules and the
  // steps, which are fixed for a command (see combinators)
  def key: Context.Key =
    (self, bound, facts, chains, diffs)

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

  // variables that occur in the facts of the context, including the primed variables of derivatives (see Diff);
  // the equations of chains.chain remain among the assumptions, unlike those of chains.replace
  def used: Set[Var] =
    facts.free ++ chains.free

  // each fact is passed to all theories;
  // equations of variables with variables and literals are recorded in the substitution only (see Chains);
  // facts are stored as given and not normalized under the substitution,
  // e.g. Simplify.implied misses (p y) when the fact is stored as (p x);
  // this is done at the top level instead: Simplify.simplify iterates to a fixpoint,
  // where the facts are the simplified siblings, which are already rewritten under the substitution
  def assume(phi: Expr): Context =
    val chains_ = chains.assume(phi)
    val diffs_ = diffs.assume(phi)

    phi match
      case Eq(e1, e2) if e1 == e2 =>
        this

      // the substitution grows only by the equation, which is then no fact, but may conflict with the conclusions
      case _ if chains_.replace.size > chains.replace.size =>
        copy(facts = facts.check(phi), chains = chains_, diffs = diffs_)

      case _ =>
        copy(facts = facts.assume(phi), chains = chains_, diffs = diffs_, rules = Context.rules(phi) ++ rules)

  // an equation lhs == rhs that is a rewrite rule of this context, e.g. one that eliminates a variable bound by a
  // combinator in favor of the outer context (see Simplify.combinator), recorded as a fact and a rule, but not in the
  // chains, whose solution of an arithmetic equation would be the other orientation
  def rule(lhs: Expr, rhs: Expr): Context =
    val phi = Eq(lhs, rhs)
    copy(facts = facts.assume(phi), diffs = diffs.assume(phi), rules = Rule(Set(), Set(), lhs, rhs, True) :: rules)

  def deny(phi: Expr): Context =
    copy(facts = facts.deny(phi), chains = chains.deny(phi), diffs = diffs.deny(phi))

  def theories: List[Theory] =
    List(facts, chains, diffs)

  def inconsistent =
    theories exists (_.inconsistent)

  // phi follows from a consistent context if denying it or assuming its negation makes one of the theories inconsistent,
  // where the negation is in normal form (see Context.not), e.g. a < b if b <= a is among the conclusions;
  // in an inconsistent context, any formula would follow, which is decided by polarity instead (see Simplify.implied);
  // an equation on Int follows from both comparisons, since a disequation is no difference constraint (see Diffs)
  def implied(phi: Expr): Boolean =
    phi match
      case Eq(left, right) if left.typ == Sort.int =>
        implied(Ints.le(left, right)) && implied(Ints.le(right, left))

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
  // whose free variables are constants, e.g. history.events == [] for delay(history.events, t);
  // it terminates, since each step removes occurrences of variables, which no other such rule matches;
  // neither side is a variable, hence the equation is not among the chains
  def rules(phi: Expr): List[Rule] =
    phi match
      case Eq(lhs, rhs) if rule(lhs, rhs) => List(Rule(Set(), Set(), lhs, rhs, True))
      case Eq(rhs, lhs) if rule(lhs, rhs) => List(Rule(Set(), Set(), lhs, rhs, True))
      case _                              => Nil

  // whether lhs == rhs is a rule of the context: rhs is ground and lhs is not;
  // equations of variables are recorded in chains, those of arithmetic are normalized instead
  def rule(lhs: Expr, rhs: Expr): Boolean =
    !lhs.isInstanceOf[Var] && !lhs.isArith && lhs.free.nonEmpty && rhs.free.isEmpty

  // the negation in normal form, independent of a context, e.g. of the conclusions among the facts and of the formulas
  // that the context decides: double negations are removed, and negated comparisons are the other comparison with
  // the arguments swapped, !(a < b) is b <= a; the simplifier may strengthen it in a context (see Simplify.not)
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

  // the parts of a context that the contexts of combinators built in it depend on (see key)
  type Key = (Option[(Expr, Expr)], List[List[Var]], Facts, Chains, Diffs)

  // the contexts of combinators by their dependencies, bound variables, and the key of the outer context
  type Combinators = Map[(List[Expr], List[Var], Key), Context]

  val empty = Context(Nil, Set(), Set(), Facts.empty, Chains.empty, Diffs.empty, None)

  // at the top of an asserted formula
  val pos = empty.copy(polarity = Some(true))
