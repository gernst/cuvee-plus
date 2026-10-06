package cuvee.simplify

import cuvee.Error
import cuvee.core._

// a conditional rewrite rule lhs = rhs if cond, whose variables xs may be instantiated by arbitrary expressions
// of the same type, and whose type parameters may be instantiated by arbitrary types;
// the other free variables are constants, e.g. those of the facts of the context (see Ctx.assume)
case class Rule(xs: List[Var], lhs: Expr, rhs: Expr, cond: Expr)

object Rule:
  // well-formedness of rules from the input, see Rules.from
  def check(rule: Rule): Rule =
    val Rule(xs, lhs, rhs, cond) = rule

    Error.report("variables of right hand side or condition do not occur in left hand side", rule):
      require(((rhs.free ++ cond.free) intersect xs.toSet) subsetOf lhs.free)

    Error.report("left hand side of rule is a variable", rule):
      require(!lhs.isInstanceOf[Var])

    Error.report("sides of rule have different types", rule):
      require(lhs.typ == rhs.typ)

    rule

  // the rule of a formula: the universally quantified variables are the variables of the rule,
  // the premise of an implication is its condition, and the conclusion must be an equation l = r,
  // an equivalence l <=> r, a negation not φ (φ = false), or a boolean atom φ (φ = true)
  // `xs` are the universally quantified variables so far, the variables of the rule
  def from(xs: List[Var], phi: Expr): Rule =
    phi match
      case All(bound, body) =>
        from(xs ++ bound, body)

      case Imp(cond, body) =>
        val Rule(_, lhs, rhs, cond_) = from(xs, body)
        Rule(xs, lhs, rhs, if cond_ == True then cond else And(cond, cond_))

      case Eq(lhs, rhs) =>
        Rule(xs, lhs, rhs, True)

      case Eqv(lhs, rhs) =>
        Rule(xs, lhs, rhs, True)

      case Not(atom) =>
        Rule(xs, atom, False, True)

      case App(fun, _, _, _) if !connectives.contains(fun.name.name) =>
        Rule(xs, phi, True, True)

      case _ =>
        Error.raise("rewrite rule is not an equation, an equivalence, a negation, or a boolean atom", phi)

  // the logical connectives, which are not boolean atoms
  val connectives = Set("and", "or", "=>", "<=>", "not", "ite", "true", "false")

object Rules:
  // the rewrite rules of the assertions and lemmas with the attribute :rw
  def from(cmds: List[Cmd]): List[Rule] =
    for case cmd @ Assert(_, _, phi, _) <- cmds if cmd.isRule
    yield
      val Rule(xs, lhs, rhs, cond) = Rule.from(Nil, phi)
      // type annotations e as T are dropped from the left-hand sides of rules, they are needed for typing only,
      // and matching would compare their types literally, which may contain the type parameters of the rule
      Rule.check(Rule(xs, lhs.removeAs, rhs, cond))
