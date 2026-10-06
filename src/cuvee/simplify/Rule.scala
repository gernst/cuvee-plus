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

  // the rules of a function definition whose body is a match on one of the formal parameters, one for each case,
  // where the pattern replaces the parameter in the left-hand side, and pattern variables that shadow
  // other parameters are renamed apart; overlapping patterns are not treated specially,
  // although the cases of a match apply in sequence
  def from(state: State, fun: Fun, body: Expr): List[Rule] =
    body match
      case Match(x: Var, cases) if fun.formals.contains(x) =>
        val others = fun.formals.filterNot(_ == x)

        for Case(pat, rhs, cond) <- cases
        yield
          val re = Subst.fresh(others.filter(pat.free.contains))
          val pat_ = re(pat)

          val args = fun.formals.map(y => if y == x then pat_ else y)
          Rule(others ++ pat_.free.toList, App(state, fun, args), re(rhs), re(cond))

      case _ =>
        Error.raise("rewrite rules of a definition need a match on a parameter", fun)

  // the logical connectives, which are not boolean atoms
  val connectives = Set("and", "or", "=>", "<=>", "not", "ite", "true", "false")

object Rules:
  // the rewrite rules of the assertions, lemmas, and function definitions with the attribute :rw
  def from(state: State, cmds: List[Cmd]): List[Rule] =
    for
      cmd <- cmds if cmd.isRule
      Rule(xs, lhs, rhs, cond) <- from(state, cmd)
    // type annotations e as T are dropped from the left-hand sides of rules, they are needed for typing only,
    // and matching would compare their types literally, which may contain the type parameters of the rule
    yield Rule.check(Rule(xs, lhs.removeAs, rhs, cond))

  def from(state: State, cmd: Cmd): List[Rule] =
    cmd match
      case Assert(_, _, phi, _)   => List(Rule.from(Nil, phi))
      case DefineFun(fun, body, _) => Rule.from(state, fun, body)
      case _                       => Nil
