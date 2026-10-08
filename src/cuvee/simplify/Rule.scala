package cuvee.simplify

import cuvee.Error
import cuvee.core._

// a conditional rewrite rule lhs = rhs if cond, whose variables vars may be instantiated by arbitrary expressions
// of the same type, and whose type parameters may be instantiated by arbitrary types;
// the other free variables are constants, e.g. those of the facts of the context (see Ctx.assume)
case class Rule(params: Set[Param], vars: Set[Var], lhs: Expr, rhs: Expr, cond: Expr):
  def removeAs =
    Rule(params, vars, lhs.removeAs, rhs, cond)

object Rule:
  // well-formedness of rules from the input, see Rules.from
  def check(rule: Rule): Rule =
    val Rule(params, vars, lhs, rhs, cond) = rule

    Error.report("variables of right hand side or condition do not occur in left hand side", rule):
      require(((rhs.free ++ cond.free) intersect vars) subsetOf lhs.free)

    Error.report("left hand side of rule is a variable", rule):
      require(!lhs.isInstanceOf[Var])

    Error.report("sides of rule have different types", rule):
      require(lhs.typ == rhs.typ)

    rule

  // the rule of a formula: the universally quantified variables are the variables of the rule,
  // the premise of an implication is its condition, and the conclusion must be an equation l = r,
  // an equivalence l <=> r, a negation not φ (φ = false), or a boolean atom φ (φ = true)
  // `vars` are the universally quantified variables so far, the variables of the rule,
  // and `cond` the conjunction of the premises so far, the condition of the rule
  def from(params: Set[Param], vars: Set[Var], cond: Expr, phi: Expr): Rule =
    phi match
      case All(bound, body) =>
        from(params, vars ++ bound, cond, body)

      case Imp(cond_, body) =>
        from(params, vars, if cond == True then cond_ else And(cond, cond_), body)

      case Eq(lhs, rhs) =>
        Rule(params, vars, lhs, rhs, cond)

      case Eqv(lhs, rhs) =>
        Rule(params, vars, lhs, rhs, cond)

      case Not(atom) =>
        Rule(params, vars, atom, False, cond)

      case App(fun, _, _, _) if !connectives.contains(fun.name.name) =>
        Rule(params, vars, phi, True, cond)

      case _ =>
        Error.raise("rewrite rule is not an equation, an equivalence, a negation, or a boolean atom", phi)

  // the rules of a function definition whose body is a match on one of the formal parameters, one for each case,
  // where the pattern replaces the parameter in the left-hand side, and pattern variables that shadow
  // other parameters are renamed apart; overlapping patterns are not treated specially,
  // although the cases of a match apply in sequence;
  // other definitions are unfolded by a single rule, which terminates for definitions that are not recursive
  def from(state: State, fun: Fun, body: Expr): List[Rule] =
    // the body refers to the formal parameters with the defined sorts expanded (see Type.expand)
    val formals = Type.expand(state, fun.formals)
    val params = fun.params.toSet

    body match
      case Match(x: Var, cases) if formals.contains(x) =>
        for Case(pat, rhs, cond) <- cases
        yield
          val index = formals.indexOf(x)
          val bound = pat.free
          val (formals_, re) = Subst.rename(formals, bound)
          val vars_ = formals_.toSet

          val args = formals_.patch(index, List(pat), 1)
          Rule(params, vars_ ++ pat.free, App(state, fun, args), rhs, cond)

      case _ =>
        List(Rule(params, formals.toSet, App(state, fun, formals), body, True))

  // the logical connectives, which are not boolean atoms
  val connectives = Set("and", "or", "=>", "<=>", "not", "ite", "true", "false")

object Rules:
  // the rewrite rules of the assertions, lemmas, and function definitions with the attribute :rw
  def from(state: State, cmds: List[Cmd]): List[Rule] =
    for
      cmd <- cmds if cmd.isRule
      rule <- from(state, cmd)
    // type annotations e as T are dropped from the left-hand sides of rules, they are needed for typing only,
    // and matching would compare their types literally, which may contain the type parameters of the rule
    yield Rule.check(rule.removeAs)

  def from(state: State, cmd: Cmd): List[Rule] =
    cmd match
      case Assert(_, params, phi, _) =>
        List(Rule.from(params.toSet, Set(), True, phi))

      case DefineFun(fun, body, _) =>
        Rule.from(state, fun, body)

      case _ =>
        Nil
