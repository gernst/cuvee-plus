package cuvee.verify

import util.Name
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._

// the steps of a path in order: fresh variables for nondeterministic choices and havoc,
// assumptions, branch conditions, and checks, e.g. of assertions and preconditions of calls
enum Step:
  case Fresh(zs: List[Var])
  case Assume(phi: Expr)
  case When(phi: Expr)
  case Check(phi: Expr)

// a path through a program by symbolic execution:
// the values of the program variables as a substitution and the steps taken, where each check
// is conditional on the assumptions and branch conditions before it;
// a path that has left by a jump (break, continue, or return) skips the remaining statements;
// depth is the number of enclosing loops, by which -teq-state tells nested loops from the outermost ones
case class Path(su: Subst[Nothing, Expr], steps: List[Step], jump: Option[Prog], depth: Int = 0):
  def apply(expr: Expr): Expr =
    su(expr)

  def apply(x: Var): Expr =
    su(x)

  def zs = steps.collect { case Step.Fresh(zs) => zs }.flatten
  def assms = steps.collect { case Step.Assume(phi) => phi }
  def branch = steps.collect { case Step.When(phi) => phi }

  // the checks, each conditional on the assumptions and branch conditions before it
  def checks: List[Expr] =
    checks(Nil, steps)

  // the checks among `steps`, each conditional on `ctx` and the assumptions and branch conditions before it
  def checks(ctx: List[Expr], steps: List[Step]): List[Expr] =
    steps match
      case Nil                      => Nil
      case Step.Assume(phi) :: rest => checks(ctx :+ phi, rest)
      case Step.When(phi) :: rest   => checks(ctx :+ phi, rest)
      case Step.Check(phi) :: rest  => Imp(And(ctx), phi) :: checks(ctx, rest)
      case Step.Fresh(_) :: rest    => checks(ctx, rest)

  // the assumptions and branch conditions, under which the path is taken
  def context: Expr =
    And(assms ++ branch)

  def assume(phi: Expr) =
    copy(steps = steps :+ Step.Assume(phi))

  def when(phi: Expr) =
    copy(steps = steps :+ Step.When(phi))

  def check(phi: Expr) =
    copy(steps = steps :+ Step.Check(phi))

  // the values of nondeterministic choices and havoc, which are quantified from here on
  def fresh(zs_ : List[Var]) =
    copy(steps = steps :+ Step.Fresh(zs_))

  def assign(xs: List[Var], es: List[Expr]) =
    copy(su = su ++ Subst.from(xs, es))

  // the assumptions A, the branch conditions B, and the checks C of this path as formulas
  def A = And(assms)
  def B = And(branch)
  def C = And(checks)

object Path:
  def apply(su: Subst[Nothing, Expr]): Path =
    Path(su, Nil, None)

  // the formula that the steps of all paths hold, where the paths share their common prefixes,
  // such that each assumption occurs once for the checks after it, e.g. a trace equation system;
  // fresh variables are quantified universally, assumptions and branch conditions are premises,
  // and checks are conjuncts
  def formula(paths: List[List[Step]]): Expr =
    val heads = paths.flatMap(_.headOption).distinct

    val conjuncts =
      for head <- heads
      yield
        val rest = formula(paths.collect { case `head` :: tail => tail })
        head match
          case Step.Fresh(zs)   => All(zs, rest)
          case Step.Assume(phi) => Imp(phi, rest)
          case Step.When(phi)   => Imp(phi, rest)
          case Step.Check(phi)  => And(List(phi, rest))

    And(conjuncts)

// verification by symbolic execution, where loops are summarized by trace equation systems
// (after Trace Equation Systems for Program Verification):
// the goal of each procedure is that for all paths through its body, all checks hold,
// and the postcondition holds if the assumptions and branch conditions do, where the paths share their prefixes;
// loops yield a path for each way to leave them, whose fresh variables are the state at the exit, the number of iterations, the traces,
// and the sequences of nondeterministic choices, which assumes the trace equation system and the negated guard,
// and which checks that the body executes safely from the current state if the guard holds;
// the goals contain the combinators trace and all, which must be rewritten before they are passed to a solver,
// except for programs without loops
object TEQ extends Transform:
  // the lemma database is injected by the source (see Config.injected)
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val gs = Type.expand(state, state.globals)
    val entry = config.entryPoint

    // the entry point must be defined by the end of the input, e.g. main in C
    if last == Done then
      for p <- entry
      do
        Error.report("entry point not defined", p.name):
          require(state.procdefs.contains(p))

    for
      cmd <- cmds
      cmd_ <- verify(config, state, gs, entry, cmd)
    yield cmd_

  // the module `name` of the lemma database (resources/cuvee/teq), a resource
  def module(name: String) =
    s"/cuvee/teq/$name.dfy"

  // the modules of the lemma database in the order in which -teq injects them, which is the order of their
  // dependencies (each refers to the declarations of the earlier ones only) and the order in which the rules are
  // tried: the core declarations (the types, the functions on traces, the shared definitions), then the lemmas on
  // arithmetic, counters, aggregation, arrays, and searching; further modules, e.g. nested (nested loops) and sorting,
  // are injected on demand by -include teq:<name>, after these
  val modules =
    List("core", "arithmetic", "counters", "aggregation", "arrays", "search").map(module)

  // the lemma database of -teq-state, a single fresh module with the core declarations that it needs and the lemmas
  // that the examples of state traces need (see ideas/state-trace.md), instead of the modules of -teq
  val stateModules =
    List("state").map(module)

  // the declarations of the functions on traces and the lemmas about them, the modules parsed in order by a fresh
  // parser for Dafny, for tests
  lazy val lemmas: List[Cmd] =
    val (_, parser, _) = cuvee.dafny.Source.newParser(Config.default)
    modules.flatMap(cuvee.dafny.Source.parse(_, parser))

  // a goal for the entry point only, if there is one (see Config.entryPoint), since calls are inlined, which checks
  // the other procedures in the context of their calls; a goal for each procedure otherwise
  def verify(config: Config, state: State, gs: List[Var], entry: Option[Name], cmd: Cmd): List[Cmd] =
    cmd match
      case DeclareProc(_, _) | DeclareVar(_, _) | AnnotateTag(_, _) =>
        Nil

      case DefineProc(Proc(name, _, _, _), _, _) if entry.exists(_ != name) =>
        Nil

      // old(e) refers to the values gs_ of the global variables at the entry, which coincide with gs initially
      case DefineProc(Proc(name, params, _, _), body, _) =>
        val (in, out, pre, post) = VCGen.contract(state, name)
        val gs_ = gs.fresh
        val body_ = Old.elim(gs, gs_, state.annotated(body))
        val post_ = Old.elim(gs, gs_, post)

        // the postcondition is the last check of each path
        val paths = symex(config, state, name, body_, Path(Subst.empty))
        val goal = Path.formula(for p <- paths yield p.check(p(post_)).steps)

        val phi = All(in ++ out ++ gs, Imp(pre, Subst.from(gs_, gs)(goal)))
        List(Assert(Goal, params, phi, Attrs.empty))

      case _ =>
        List(cmd)

  def symex(config: Config, state: State, proc: Name, progs: List[Prog], p: Path): List[Path] =
    progs.foldLeft(List(p)):
      case (paths, prog) =>
        paths.flatMap(symex(config, state, proc, prog, _))

  // the paths through `prog` that extend `p`
  def symex(config: Config, state: State, proc: Name, prog: Prog, p: Path): List[Path] =
    if p.jump.isDefined
    then List(p)
    else
      prog match
        // break and continue occur inside of loops only (see Type.check), which resolve them
        case Break | Continue | Return =>
          List(p.copy(jump = Some(prog)))

        case Spec(xs, pre, post) =>
          val zs = xs.fresh
          val p_ = p.check(p(pre)).fresh(zs).assign(xs, zs)
          List(p_.assume(p_(post)))

        case Assign(xs, rhs) =>
          List(p.assign(xs, rhs.map(p(_))))

        case call: Call =>
          this.call(config, state, proc, call, p)

        // locals have arbitrary initial values, the values of variables they shadow are restored afterwards
        case Block(locals, progs, _) =>
          val zs = locals.fresh
          val outer = locals.map(x => x -> p.su.vars.get(x))
          for p_ <- symex(config, state, proc, progs, p.fresh(zs).assign(locals, zs))
          yield
            val su = outer.foldLeft(p_.su):
              case (su, (x, Some(e))) => su + (x -> e)
              case (su, (x, None))    => su - x
            p_.copy(su = su)

        case If(test, left, right) =>
          val test_ = p(test)
          symex(config, state, proc, left, p.when(test_)) ++ symex(config, state, proc, right, p.when(Not(test_)))

        // nondeterministic choices are branches on fresh boolean variables, which keeps branch conditions disjoint
        case Choice(progs) =>
          choice(config, state, proc, progs, p)

        case While(test, body, attrs) =>
          loop(config, state, proc, Some(test), body, attrs, p)

        case Iter(body, attrs) =>
          loop(config, state, proc, None, body, attrs, p)

        case _: Ode | _: Par =>
          Error.raise("differential equations and parallel composition not supported by symbolic execution", proc)

  def choice(config: Config, state: State, proc: Name, progs: List[Prog], p: Path): List[Path] =
    progs match
      case Nil =>
        Nil

      case List(prog) =>
        symex(config, state, proc, prog, p)

      case prog :: rest =>
        val z = Var("choice", Sort.bool).fresh
        val p_ = p.fresh(List(z))
        symex(config, state, proc, prog, p_.when(z)) ++ choice(config, state, proc, rest, p_.when(Not(z)))

  // calls are inlined, which requires procedures without a contract, e.g. functions in C:
  // the paths through the body of the callee, like a block whose locals are the formal parameters:
  // the inputs are the values of the arguments, the outputs are arbitrary initially, a return leaves the callee only,
  // and the variables of the caller with the same names are restored afterwards, before the results are assigned;
  // calls of recursive procedures do not terminate
  def call(config: Config, state: State, proc: Name, call: Call, p: Path): List[Path] =
    val Call(name, args, res) = call
    val (in, out, pre, post) = VCGen.contract(state, name)

    Error.report("calls of procedures with a contract are not supported", name):
      require(pre == True && post == True)

    Error.report("procedure without body", name):
      require(state.procdefs contains name)

    val zs = out.fresh
    val outer = (in ++ out).map(x => x -> p.su.vars.get(x))
    val entry = p.fresh(zs).assign(in ++ out, args.map(p(_)) ++ zs)

    for q <- symex(config, state, name, state.procdefs(name), entry)
    yield
      val values = out.map(q(_))
      val su = outer.foldLeft(q.su):
        case (su, (x, Some(e))) => su + (x -> e)
        case (su, (x, None))    => su - x
      q.copy(su = su, jump = None).assign(res, values)

  // the variables modified by a loop body, the global ones are those in the modifies clause of the loop (see Type.check)
  def modified(body: Prog, attrs: Attrs): List[Var] =
    (body.mod ++ attrs.modifies).toList.distinct

  // the trace equation system of a loop and the paths that leave it, which summarize all paths through the loop:
  // the iterations take the paths through the body that end normally or by continue,
  // the loop is left if the guard does not hold, where loops without test (nondeterministic iterations)
  // may be left in every iteration, or by a path through the body that ends by break or return
  def loop(config: Config, state: State, proc: Name, test: Option[Expr], body: Prog, attrs: Attrs, p: Path): List[Path] =
    val xs = modified(body, attrs)
    val guard = test.getOrElse(True)

    // the body from an arbitrary state x♯ of the loop variables, the other variables keep their values
    val sharp = xs.fresh
    val inner = Path(p.su ++ Subst.from(xs, sharp)).copy(depth = p.depth + 1)
    val paths = symex(config, state, proc, body, inner).filter(iterates)

    // no path through the body leads to another iteration, e.g. a body that ends by break or return on all paths:
    // the loop runs the body at most once, as a conditional, without a trace equation system, where the paths that
    // end by break continue after the loop, and loops without test may also be left before the body
    if paths.isEmpty
    then
      val guard_ = p(guard)
      val once =
        for q <- symex(config, state, proc, body, if test.isDefined then p.when(guard_) else p)
        yield if q.jump == Some(Return) then q else q.copy(jump = None)

      test match
        case Some(_) => once :+ p.when(Not(guard_))
        case None    => p :: once
    else
      // the nondeterministic choices of the body are ranged over by lists, named after them with a final ?, e.g. Choice?
      val zs = paths.flatMap(_.zs).distinct
      val Zs = zs.map(z => Var(z.name.name.capitalize + "?", Sort.list(z.typ)).fresh)

      // the number of iterations, a natural, whose value is nonnegative as an integer, an atom of arithmetic
      val n = Var("n", Sort.nat).fresh
      val k = Var("k", Sort.int).fresh
      val K = Var("K", Sort.trace(Sort.int)).fresh
      // all earlier iterations have taken some path through the body, with the guard holding before each of them
      val paths_ = Or(for q <- paths yield And(List(q.A, q.B, q.C).flatMap(And.flattenStrong)))
      val constraint = And(List(inner(guard), paths_).flatMap(And.flattenStrong))

      // the per-variable form of the paper, or the state form of -teq-state over the tuples of the prelude (see
      // transform.StateTEQ), which is closed for nested loops: the counter, the trace and the exit values are
      // substituted by their definitions, such that only the number of iterations and the choices are fresh
      val (fresh, cur, teq) =
        if config.stateTraces
        then cuvee.transform.StateTEQ.system(state, xs, sharp, zs, Zs, n, k, K, paths, constraint, p, closed = p.depth > 0)
        else system(xs, sharp, zs, Zs, n, k, K, paths, constraint, p)

      // the state at the exit, from which the body executes safely if the guard holds,
      // the paths of the body from there that end by break or return leave the loop as well
      val exit = p.fresh(fresh).assign(xs, cur)
      val last = symex(config, state, proc, body, Path(exit.su).copy(depth = p.depth + 1))
      val safe = Path.formula(last.map(_.steps))
      val exit_ = exit.assume(teq)
      val guard_ = exit_(guard)
      val checked = if safe == True then exit_ else exit_.check(Imp(guard_, safe))

      // the exits are told apart by branch conditions, the negated test and the guard before a break or return,
      // which an enclosing loop takes as the guards of the cases of its updates (Upd(q.B, ...)), such that these are
      // disjoint, otherwise exits with different values would give contradicting cases
      val left =
        for q <- last if !iterates(q)
        yield
          val jump = if q.jump == Some(Return) then q.jump else None
          Path(q.su, checked.steps ++ (Step.When(guard_) :: q.steps), jump)

      test match
        case Some(test) =>
          checked.when(Not(exit_(test))) :: left

        case None =>
          checked :: left

  // the trace equation system of the paper (definition 4.4): one trace per modified variable x, named after it,
  // capitalized, e.g. I for i, whose update has a case for each path, with the other loop variables and the choices it
  // uses as dependencies; the current values; the counter; and the iteration constraint over all traces and choices;
  // the fresh variables of the exit, the exit values of the loop variables, and the system
  def system(
      xs: List[Var],
      sharp: List[Var],
      zs: List[Var],
      Zs: List[Var],
      n: Var,
      k: Var,
      K: Var,
      paths: List[Path],
      constraint: Expr,
      p: Path
  ): (List[Var], List[Expr], Expr) =
    val Xs = xs.map(x => Var(x.name.name.capitalize, Sort.trace(x.typ)).fresh)
    val cur = xs.fresh

    val equations =
      for ((x, x_), tr) <- xs zip sharp zip Xs
      yield
        val updates = for q <- paths yield Upd(q.B, q(x))
        val used = updates.free
        val others = (sharp zip Xs).filter((y_, _) => y_ != x_ && used.contains(y_))
        val choices = (zs zip Zs).filter((z, _) => used.contains(z))
        val deps = Butlast(K) :: others.map((_, tr_) => Butlast(tr_)) ++ choices.map(_._2)
        val bound = k :: others.map(_._1) ++ choices.map(_._1)
        Eq(tr, Trace(p(x), deps, x_, bound, update(updates)))

    val counter = Eq(K, Counter(Ints.zero, Ints.one, n))
    val current = for (x, tr) <- cur zip Xs yield Eq(x, Current(tr))
    val iterations = Invs(Butlast(K) :: Xs.map(Butlast(_)) ++ Zs, k :: sharp ++ zs, constraint)

    (cur ++ List(n, K) ++ Xs ++ Zs, cur, And(counter :: current ++ equations ++ List(iterations, Ints.le(Ints.zero, Nats.integer(n)))))

  // a single unconditional case is its result
  def update(updates: List[Upd]): Expr =
    updates match
      case List(Upd(True, rhs)) => rhs
      case _                    => Eps(updates)

  // the paths through a loop body that lead to the next iteration, i.e., that end normally or by continue
  def iterates(q: Path): Boolean =
    q.jump.isEmpty || q.jump == Some(Continue)
