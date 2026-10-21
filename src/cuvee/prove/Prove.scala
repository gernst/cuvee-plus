package cuvee.prove

import cuvee.Config
import cuvee.Error
import cuvee.sexpr
import cuvee.pipe.Transform
import cuvee.core._

// the deduction engine of -prove (see doc/prove.md and doc/prove.md): the assertions and
// lemmas with the attribute :rw so far are rewrite rules and those with :fw forward lemmas (see Forward), which are
// kept as they are, the goals and the other
// assertions are simplified under a context of congruence classes and linear constraints with these rules (see
// Simplify, Rewrite, Context), each with a fresh number of rewrite steps; goals that simplify to true are dropped;
// like -simplify, with -rules the rules applied follow each assertion as (set-info :used ((name count) ...))
object Prove extends Transform:
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): (List[Cmd], Option[Cmd]) =
    val rules = Rules.from(state, prefix ++ cmds)
    val forward = Forward.from(prefix ++ cmds)

    def fresh() = Context.empty(state).withRules(rules).copy(forward = forward)

    val cmds_ =
      for
        cmd <- cmds
        ctx = fresh()
        cmd_ <- if cmd.isRule || Forward.is(cmd) then List(cmd) else counterexample(config, state, fresh, cases(config, state, fresh, Simplify.simplify(config, state, ctx, cmd), 4)) :: used(config, ctx, cmd)
        if !isTrivial(cmd_)
      yield cmd_

    (cmds_, Some(last))

  // a goal that remains is proved by cases (see alternatives), each case with a context of its own, at most `depth`
  // splits deep; it is kept as it is unless all cases hold, so that the output does not multiply
  def cases(config: Config, state: State, fresh: () => Context, cmd: Cmd, depth: Int): Cmd =
    cmd match
      case Assert(justify, params, phi, attrs) if depth > 0 =>
        alternatives(phi) match
          case Some(phis) if phis.forall(phi_ => isTrivial(cases(config, state, fresh, Simplify.simplify(config, state, fresh(), Assert(justify, params, phi_, attrs)), depth - 1))) =>
            Assert(justify, params, True, attrs)

          case _ =>
            cmd

      case _ =>
        cmd

  // a goal that remains and has no traces, lists, or other functions than those of arithmetic and logic left, e.g.
  // forall N :: !(0 < N && N <= 536870911) of an unsafe task, is refuted by a counterexample among small values and
  // the literals of the goal, plus or minus 1, which its instance evaluates to false at: the goal is false then, which
  // -verify answers with incorrect unless the goal is :abstract (see pipe.Verify); at most four variables
  def counterexample(config: Config, state: State, fresh: () => Context, cmd: Cmd): Cmd =
    cmd match
      case Assert(justify, Nil, phi, attrs) if phi != True && phi != False =>
        val (xs, body) =
          phi match
            case All(xs, body) => (xs, body)
            case _             => (Nil, phi)

        val scalar = xs.forall(x => x.typ == Sort.int || x.typ == Sort.nat || x.typ == Sort.bool)
        if xs.length > 4 || !scalar || !evaluable(body) || !body.free.subsetOf(xs.toSet)
        then cmd
        else
          val ints = (literals(body) ++ List(BigInt(0), BigInt(1), BigInt(-1))).flatMap(c => List(c - 1, c, c + 1)).distinct.take(24)
          val choices =
            for x <- xs
            yield
              if x.typ == Sort.bool then List(True, False)
              else if x.typ == Sort.nat then ints.filter(_ >= 0).map(c => Nats.natural(Lit(c, Sort.int)))
              else ints.map(c => Lit(c, Sort.int))

          val refuted = assignments(choices).take(4096).exists(values => Simplify.simplify(config, state, fresh(), Subst.from(xs, values)(body)) == False)
          if refuted then Assert(justify, Nil, False, attrs) else cmd

      case _ =>
        cmd

  // the functions whose values are computed from literals, without quantifiers
  val computed = Set("and", "or", "not", "=>", "=", "distinct", "<", "<=", ">", ">=", "+", "-", "*", "div", "mod", "ite", "true", "false", "integer", "natural", "zero", "succ")

  def evaluable(expr: Expr): Boolean =
    expr match
      case _: Var | _: Lit           => true
      case App(fun, _, _, args)      => computed.contains(fun.name.name) && args.forall(evaluable)
      case _                         => false

  def literals(expr: Expr): List[BigInt] =
    expr match
      case Lit(value: BigInt, _) => List(value)
      case App(_, _, _, args)    => args.flatMap(literals)
      case _                     => Nil

  def assignments(choices: List[List[Expr]]): LazyList[List[Expr]] =
    choices match
      case Nil          => LazyList(Nil)
      case xs :: rest   => for x <- LazyList.from(xs); tail <- assignments(rest) yield x :: tail

  // the goals whose conjunction is equivalent to forall xs. φ₁ && ... && φₙ ==> ψ, tried in this order:
  // - the cases of the first premise that is a disjunction of at most three formulas, e.g. n == zero || integer(n) < 1
  //   that the rules of mods introduce (in-de41);
  // - the cases c and !c of the first guard c of an update that a case split decides (see conditions), e.g. the
  //   guard tmp % 2 == 0 of the update of a loop that does not change tmp (diamond_1-1); -split does not reach into
  //   the updates of traces, but splits the other disjunctions and if-then-else itself;
  // - the cases x % m == 0, ..., x % m == m - 1 of the first remainder by a literal 2 <= m <= 4 whose variables are
  //   free in the goal, which the simplex does not enumerate, since it is rational (see remainders), e.g. the goal
  //   !(tmp % 2 == 0) ==> tmp % 2 == 1 of the odd case of diamond_1-1
  def alternatives(phi: Expr): Option[List[Expr]] =
    phi match
      case All(xs, body) =>
        alternatives(body).map(_.map(All(xs, _)))

      case _ =>
        val (premises, concl) =
          phi match
            case Imp(ante, concl) => (And.flatten(ante), concl)
            case _                => (Nil, phi)

        premises.indexWhere(premise => Or.flatten(premise).length.min(4) match { case 2 | 3 => true; case _ => false }) match
          case -1 =>
            conditions(phi, phi.free) match
              case c :: _ =>
                Some(List(Imp(And(premises :+ c), concl), Imp(And(premises :+ Not(c)), concl)))

              case Nil =>
                for (r, m) <- remainders(phi, phi.free).headOption
                yield for i <- List.range(BigInt(0), m) yield Imp(And(premises :+ Eq(r, Ints.num(i))), concl)

          case i =>
            Some(for disjunct <- Or.flatten(premises(i)) yield Imp(And(premises.patch(i, List(disjunct), 1)), concl))

  // the remainders x % m by a literal 2 <= m <= 4 in `expr` whose variables are among `outer`, with m, whose values
  // are 0, ..., m - 1 (the remainder of SMT-LIB is not negative)
  def remainders(expr: Expr, outer: Set[Var]): List[(Expr, BigInt)] =
    val found = collection.mutable.ListBuffer[(Expr, BigInt)]()

    def visit(expr: Expr): Expr =
      expr match
        case Ints.mod(arg, Ints.num(m: BigInt)) if 2 <= m && m <= 4 && arg.free.nonEmpty && arg.free.subsetOf(outer) => found += ((expr, m))
        case _ =>
      expr.map(visit)

    visit(expr)
    found.toList.distinct

  // the conditions of `expr` that a case split may decide, in the order of their occurrence: the atoms of the guards
  // of updates whose variables are among `outer`, i.e., that depend on no bound variable of a trace or a quantifier,
  // such that each case fixes the branch everywhere, e.g. tmp % 2 == 0 in the update of a loop that does not change
  // tmp
  def conditions(expr: Expr, outer: Set[Var]): List[Expr] =
    val found = collection.mutable.ListBuffer[Expr]()

    def atoms(cond: Expr): Unit =
      for conjunct <- And.flatten(cond)
      do
        val atom = conjunct match { case Not(arg) => arg; case _ => conjunct }
        if atom != True && atom != False && atom.free.nonEmpty && atom.free.subsetOf(outer) then found += atom

    def visit(expr: Expr): Expr =
      expr match
        case Eps(upds) => upds.foreach(upd => atoms(upd.cond))
        case _         =>
      expr.map(visit)

    visit(expr)
    found.toList.distinct

  def used(config: Config, ctx: Context, cmd: Cmd): List[Cmd] =
    cmd match
      case _: Assert if config.rules =>
        val counts = ctx.applied.value.toList.groupMapReduce(_._1)(_._2)(_ + _).toList.sorted
        if counts.isEmpty then Nil
        else List(SetInfo("used", counts.map((name, n) => List(sexpr.Id(name), sexpr.Num(n.toString)))))

      case _ =>
        Nil

  def isTrivial(cmd: Cmd) =
    cmd match
      case Assert(_, _, True, _) => true
      case _                     => false
