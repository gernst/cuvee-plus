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
// a path that has left by a jump (break, continue, or return) skips the remaining statements
case class Path(su: Map[Var, Expr], steps: List[Step], jump: Option[Prog]):
  def apply(expr: Expr): Expr =
    Subst[Type, Expr](Map(), su)(expr)

  def apply(x: Var): Expr =
    su.getOrElse(x, x)

  def zs = steps.collect { case Step.Fresh(zs) => zs }.flatten
  def assms = steps.collect { case Step.Assume(phi) => phi }
  def branch = steps.collect { case Step.When(phi) => phi }

  // the checks, each conditional on the assumptions and branch conditions before it
  def checks: List[Expr] =
    val (_, checks) =
      steps.foldLeft((List[Expr](), List[Expr]())):
        case ((ctx, checks), Step.Assume(phi) ) => (ctx :+ phi, checks)
        case ((ctx, checks), Step.When(phi))    => (ctx :+ phi, checks)
        case ((ctx, checks), Step.Check(phi))   => (ctx, checks :+ Imp(And(ctx), phi))
        case ((ctx, checks), Step.Fresh(_))     => (ctx, checks)
    checks

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
    copy(su = su ++ (xs zip es))

  // the assumptions A, the branch conditions B, and the checks C of this path as formulas
  def A = And(assms)
  def B = And(branch)
  def C = And(checks)

object Path:
  def apply(su: Map[Var, Expr]): Path =
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
          case Step.Fresh(zs)   => if rest == True then True else All(zs, rest)
          case Step.Assume(phi) => if rest == True then True else Imp(phi, rest)
          case Step.When(phi)   => if rest == True then True else Imp(phi, rest)
          case Step.Check(phi)  => And(phi :: And.flattenStrong(rest))

    And(conjuncts.flatMap(And.flattenStrong))

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
  // the lemma database is injected once at the beginning, i.e., when nothing has been passed through so far
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val gs = state.globals

    val cmds_ =
      for
        cmd <- cmds
        cmd_ <- verify(state, gs, cmd)
      yield cmd_

    if prefix.isEmpty
    then lemmas ++ cmds_
    else cmds_

  // the declarations of the functions on traces and the lemmas about them (resources/cuvee/teq.dfy),
  // which are parsed by a fresh parser for Dafny
  lazy val lemmas: List[Cmd] =
    val (_, parser, _) = cuvee.dafny.Source.newParser()
    cuvee.dafny.Source.parse("/cuvee/teq.dfy", parser)

  def verify(state: State, gs: List[Var], cmd: Cmd): List[Cmd] =
    cmd match
      case DeclareProc(_, _) | DeclareVar(_, _) =>
        Nil

      // old(e) refers to the values gs_ of the global variables at the entry, which coincide with gs initially
      case DefineProc(Proc(name, params, _, _), body, _) =>
        val (in, out, pre, post) = Verify.contract(state, name)
        val gs_ = gs.fresh
        val body_ = Old.elim(gs, gs_, body)
        val post_ = Old.elim(gs, gs_, post)

        // the postcondition is the last check of each path
        val paths = symex(state, name, body_, Path(Map()))
        val goal = Path.formula(for p <- paths yield p.check(p(post_)).steps)

        val phi = All(in ++ out ++ gs, Imp(pre, Subst.from(gs_, gs)(goal)))
        List(Assert(Goal, params, phi, Attrs.empty))

      case _ =>
        List(cmd)

  def symex(state: State, proc: Name, progs: List[Prog], p: Path): List[Path] =
    progs.foldLeft(List(p)):
      case (paths, prog) =>
        paths.flatMap(symex(state, proc, prog, _))

  // the paths through `prog` that extend `p`
  def symex(state: State, proc: Name, prog: Prog, p: Path): List[Path] =
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
          List(this.call(state, proc, call, p))

        // locals have arbitrary initial values, the values of variables they shadow are restored afterwards
        case Block(locals, progs) =>
          val zs = locals.fresh
          val outer = locals.map(x => x -> p.su.get(x))
          for p_ <- symex(state, proc, progs, p.fresh(zs).assign(locals, zs))
          yield
            val su = outer.foldLeft(p_.su):
              case (su, (x, Some(e))) => su + (x -> e)
              case (su, (x, None))    => su - x
            p_.copy(su = su)

        case If(test, left, right) =>
          val test_ = p(test)
          symex(state, proc, left, p.when(test_)) ++ symex(state, proc, right, p.when(Not(test_)))

        // nondeterministic choices are branches on fresh boolean variables, which keeps branch conditions disjoint
        case Choice(progs) =>
          choice(state, proc, progs, p)

        case While(test, body, attrs) =>
          loop(state, proc, Some(test), body, attrs, p)

        case Iter(body, attrs) =>
          loop(state, proc, None, body, attrs, p)

        case _: Ode | _: Par =>
          Error.raise("not supported by symbolic execution", prog)

  def choice(state: State, proc: Name, progs: List[Prog], p: Path): List[Path] =
    progs match
      case Nil =>
        Nil

      case List(prog) =>
        symex(state, proc, prog, p)

      case prog :: rest =>
        val z = Var("choice", Sort.bool).fresh
        val p_ = p.fresh(List(z))
        symex(state, proc, prog, p_.when(z)) ++ choice(state, proc, rest, p_.when(Not(z)))

  // calls by contract: the precondition is checked, as well as the measure for recursive calls,
  // the results and modified global variables are fresh,
  // and the postcondition is assumed, where old(e) refers to the values before the call
  def call(state: State, proc: Name, call: Call, p: Path): Path =
    val Call(name, args, res) = call
    val (in, out, pre, post) = Verify.contract(state, name)

    Error.report("wrong number of arguments or results in call", name, args, res):
      require(in.length == args.length && out.length == res.length)

    val mod = state.procattrs(name).modifies
    val args_ = args.map(p(_))
    val res_ = res.fresh
    val mod_ = mod.fresh

    val before = Subst.from(in ++ mod, args_ ++ mod.map(p(_)))
    val after = Subst.from(in ++ out ++ mod, args_ ++ res_ ++ mod_)
    val mod0 = mod.fresh
    val post_ = Subst.from(mod0, mod.map(p(_)))(after(Old.elim(mod, mod0, post)))

    // recursive calls must decrease the measure, whose values at the entry of `proc` are those of its inputs
    val dec =
      if name == proc
      then
        val dec = Verify.measure(state, proc)
        Verify.decreases(dec.map(before(_)), dec)
      else True

    p.check(And(before(pre), dec)).fresh(res_ ++ mod_).assign(res ++ mod, res_ ++ mod_).assume(post_)

  // the variables modified by a loop body, the global ones are those in the modifies clause of the loop (see Type.check)
  def modified(body: Prog, attrs: Attrs): List[Var] =
    (body.mod ++ attrs.modifies).toList.distinct

  // the trace equation system of a loop and the paths that leave it, which summarize all paths through the loop:
  // the iterations take the paths through the body that end normally or by continue,
  // the loop is left if the guard does not hold, where loops without test (nondeterministic iterations)
  // may be left in every iteration, or by a path through the body that ends by break or return
  def loop(state: State, proc: Name, test: Option[Expr], body: Prog, attrs: Attrs, p: Path): List[Path] =
    val xs = modified(body, attrs)
    val guard = test.getOrElse(True)

    // the body from an arbitrary state x♯ of the loop variables, the other variables keep their values
    val sharp = xs.fresh
    val inner = Path(p.su ++ (xs zip sharp))
    val paths = symex(state, proc, body, inner).filter(iterates)

    // the nondeterministic choices of the body are ranged over by sequences, named after them with a final ?, e.g. Choice?
    val zs = paths.flatMap(_.zs).distinct
    val Zs = zs.map(z => Var(z.name.name.capitalize + "?", Sort.seq(z.typ)).fresh)

    val n = Var("n", Sort.int).fresh
    val k = Var("k", Sort.int).fresh
    val K = Var("K", Sort.trace(Sort.int)).fresh
    // the traces are named after the variables, capitalized, e.g. I for i
    val Xs = xs.map(x => Var(x.name.name.capitalize, Sort.trace(x.typ)).fresh)
    val cur = xs.fresh

    // the update of x_j has a case for each path, the dependencies are the other loop variables and choices it uses
    val equations =
      for ((x, x_), tr) <- xs zip sharp zip Xs
      yield
        val updates = for q <- paths yield Upd(q.B, q(x))
        val used = updates.free
        val others = (sharp zip Xs).filter((y_, _) => y_ != x_ && used.contains(y_))
        val choices = (zs zip Zs).filter((z, _) => used.contains(z))
        val deps = Butlast(K) :: others.map((_, tr_) => Butlast(tr_)) ++ choices.map(_._2)
        val bound = k :: others.map(_._1) ++ choices.map(_._1)
        Eq(tr, Trace(p(x), deps, x_, bound, updates))

    val counter = Eq(K, Counter(Zero.int, One.int, n))
    val current = for (x, tr) <- cur zip Xs yield Eq(x, Current(tr))

    // all earlier iterations have taken some path through the body, with the guard holding before each of them
    val iterations =
      val deps = Butlast(K) :: Xs.map(Butlast(_)) ++ Zs
      val bound = k :: sharp ++ zs
      val paths_ = Or(for q <- paths yield And(List(q.A, q.B, q.C).flatMap(And.flattenStrong)))
      Invs(deps, bound, And(List(inner(guard), paths_).flatMap(And.flattenStrong)))

    val wf = Le.int(Zero.int, n) :: Zs.map(seq => Eq(Length(seq), n))
    val teq = And(counter :: current ++ equations ++ (iterations :: wf))

    // the state at the exit, from which the body executes safely if the guard holds,
    // the paths of the body from there that end by break or return leave the loop as well
    val exit = p.fresh(cur ++ List(n, K) ++ Xs ++ Zs).assign(xs, cur)
    val last = symex(state, proc, body, Path(exit.su))
    val safe = Path.formula(last.map(_.steps))
    val exit_ = exit.assume(teq)
    val guard_ = exit_(guard)
    val checked = if safe == True then exit_ else exit_.check(Imp(guard_, safe))

    val left =
      for q <- last if !iterates(q)
      yield
        val jump = if q.jump == Some(Return) then q.jump else None
        Path(q.su, checked.steps ++ (Step.Assume(guard_) :: q.steps), jump)

    test match
      case Some(test) =>
        checked.assume(Not(exit_(test))) :: left

      case None =>
        checked :: left

  // the paths through a loop body that lead to the next iteration, i.e., that end normally or by continue
  def iterates(q: Path): Boolean =
    q.jump.isEmpty || q.jump == Some(Continue)
