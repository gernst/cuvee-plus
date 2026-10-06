package cuvee.verify

import util.Name
import util.Ref
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.core.Attrs

// verification conditions by weakest preconditions: each procedure definition is replaced by the goal
// that its precondition implies the weakest precondition of its body for its postcondition (see wp)
object Verify extends Transform:
  // the global variables gs are computed once and passed to the generation of the verification conditions
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    val gs = state.globals

    for
      cmd <- cmds;
      cmd_ <- verify(state, gs, cmd)
    yield cmd_

  // the goals of a command, the other commands are kept
  def verify(state: State, gs: List[Var], cmd: Cmd): List[Cmd] =
    cmd match
      // procedures without body have nothing to verify,
      // their contract is looked up from the state at call sites
      case DeclareProc(proc, attrs) =>
        Nil

      // global variables are quantified in the goals, like the parameters of the procedures
      case DeclareVar(x, attrs) =>
        Nil

      // old(e) in the body and in the postcondition refers to the values gs_ of the global variables at the entry,
      // which are never modified and coincide with gs initially
      case DefineProc(Proc(name, params, _, _), body, _) =>
        val (in, out, pre_, post) = contract(state, name)
        val gs_ = gs.fresh

        // the body may assume the assumption initially, its commitment is checked at send and receive,
        // and both are needed for parallel compositions in the body (see wp)
        val (assume, commit) = ac(state, name, in)
        val pre = And(pre_, assume)

        val body_ = Old.elim(gs, gs_, body)
        val post_ = Old.elim(gs, gs_, post)
        val phi = wp(state, gs, name, assume, commit, body_, post_, False, False, post_)
        val phi_ = All(in ++ out ++ gs, Imp(pre, Subst.from(gs_, gs)(phi)))
        List(Assert(Goal, params, phi_, Attrs.empty))

      case _ =>
        List(cmd)

  // formal parameters, precondition, and postcondition of procedure `name`
  def contract(state: State, name: Name): (List[Var], List[Var], Expr, Expr) =
    Error.report("procedure not declared", name):
      require(state.procs.contains(name))

    val Proc(_, _, in, out) = state.procs(name)
    val attrs = state.procattrs(name)
    (in, out, attrs.requires, attrs.ensures)

  // the termination measure of procedure `name`, the components of a lexicographic order,
  // which is evaluated at the entry of the procedure, therefore it must refer to the inputs only,
  // which are never modified
  def measure(state: State, name: Name): List[Expr] =
    val Proc(_, _, in, _) = state.procs(name)
    val dec = state.procattrs(name).decreases

    Error.report("termination measure refers to variables other than the inputs", name, dec):
      require(dec.free subsetOf in.toSet)

    dec

  // `next` is smaller than `prev` in the lexicographic order over the integers bounded from below by 0,
  // as in Dafny, i.e., some component decreases and is nonnegative before, and all components before it are equal;
  // without a measure, termination is not checked
  def decreases(next: List[Expr], prev: List[Expr]): Expr =
    Error.report("termination measures of different lengths", next, prev):
      require(next.length == prev.length)

    if prev.isEmpty
    then True
    else
      val cases =
        for i <- prev.indices.toList
        yield And(Eq(next.take(i), prev.take(i)) ++ List(Le.int(Zero.int, prev(i)), Lt.int(next(i), prev(i))))
      Or(cases)

  // weakest preconditions need a separate postcondition for each way a program can terminate:
  // normally, by break, by continue, and by return;
  // `proc` is the procedure that contains the program, whose recursive calls must decrease its measure,
  // `assume` and `commit` are its assumption and commitment (true if there are none)
  def wp(state: State, gs: List[Var], proc: Name, assume: Expr, commit: Expr, progs: List[Prog], post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
    progs.foldRight(post):
      case (prog, phi) =>
        wp(state, gs, proc, assume, commit, prog, phi, break, continue, return_)

  def wp(state: State, gs: List[Var], proc: Name, assume: Expr, commit: Expr, prog: Prog, post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
    prog match
      case Break =>
        break

      case Continue =>
        continue

      case Return =>
        return_

      case Spec(xs, pre, phi) =>
        And(pre, All(xs, Imp(phi, post)))

      case Assign(xs, rhs) =>
        val su = Subst.from(xs, rhs)
        su(post)

      // send, receive, and tick assert the commitment of the enclosing procedure for the extended history
      // and assume it afterwards, i.e., the commitment must hold in addition to `post` after the call;
      // communication is joint, the event of a receive is that of the matching send of another process,
      // hence the commitment is made first also after receiving, since a commitment must always be made
      // before an assumption is taken, which is justified by the commitments of the other processes (see par)
      case Send(call) =>
        this.call(state, proc, call, And(commit, post))

      case Recv(call) =>
        this.call(state, proc, call, And(commit, post))

      case Tick(call) =>
        this.call(state, proc, call, And(commit, post))

      case call: Call =>
        this.call(state, proc, call, post)

      case Block(locals, progs) =>
        // locals may shadow variables in the postcondition, therefore they are renamed apart
        val (locals_, su) = Subst.rename(locals)
        All(locals_, wp(state, gs, proc, assume, commit, su(progs), post, break, continue, return_))

      case Choice(progs) =>
        And(progs.map(wp(state, gs, proc, assume, commit, _, post, break, continue, return_)))

      case If(test, left, right) =>
        val left_ = Imp(test, wp(state, gs, proc, assume, commit, left, post, break, continue, return_))
        val right_ = Imp(Not(test), wp(state, gs, proc, assume, commit, right, post, break, continue, return_))
        And(left_, right_)

      case While(test, body, attrs) =>
        loop(state, gs, proc, assume, commit, Some(test), body, attrs, post, return_)

      case Iter(body, attrs) =>
        loop(state, gs, proc, assume, commit, None, body, attrs, post, return_)

      // the time starts at 0 and evolves along with the variables, with derivative 1, hence it stays nonnegative,
      // afterwards the history, if any, ticks by the time that has passed (see Tick)
      case Ode(time, xs, rhs, dom, attrs) =>
        val t = time.fresh
        val su = Subst.from(List(time), List(t))
        val after = tick(state, t) match
          case Some(call) => wp(state, gs, proc, assume, commit, call, post, break, continue, return_)
          case None       => post
        val phi = ode(t :: xs, One.real :: su(rhs), And(Le.real(Zero.real, t), su(dom)), attrs.invariants.map(su(_)), after)
        Subst.from(List(t), List(Zero.real))(phi)

      // the parallel composition relies on the assumption of the enclosing procedure
      // and must establish its commitment (see par)
      case Par(calls) =>
        par(state, gs, proc, assume, commit, calls, post)

  // calls by the contract of the procedure, where the measure of `proc` must decrease on recursive calls
  def call(state: State, proc: Name, call: Call, post: Expr): Expr =
    val (pre, fresh, phi, rename) = instance(state, proc, call)
    And(pre, All(fresh, Imp(phi, rename(post))))

  // the contract of procedure `name` instantiated for a call: the precondition, which includes the decrease of the
  // measure of `proc` on recursive calls, the fresh values of the results and the modified global variables,
  // the postcondition over them, and the renaming of the results and modified variables to these values
  def instance(state: State, proc: Name, call: Call): (Expr, List[Var], Expr, Subst[Nothing, Var]) =
    val Call(name, args, res) = call
    val (in, out, pre, phi) = contract(state, name)

    Error.report("wrong number of arguments or results in call", name, args, res):
      require(in.length == args.length && out.length == res.length)

    // results and the modified global variables are fresh since `args` may refer to their old values,
    // the precondition refers to the values of the global variables before the call,
    // as does old(e) in the postcondition, whose modified global variables are kept apart as mod0 meanwhile
    val mod = state.procattrs(name).modifies
    val (vars_, rename) = Subst.rename(res ++ mod)
    val mod0 = mod.fresh
    // the substitutions replace the formal parameters and instantiate the type parameters of a polymorphic procedure
    // by the types of the arguments, and those of the results, which su_ replaces in addition
    val su = Ref(Subst.empty[Type, Expr])
    Type.bind(state, in, args, su)
    val su_ = su.copy
    Type.bind(state, out ++ mod, vars_, su_)
    val phi_ = Subst.from(mod0, mod)(su_(Old.elim(mod, mod0, phi)))

    // the measure refers to the inputs, whose values at the call are those at the entry of `proc`
    val dec =
      if name == proc
      then
        val dec = measure(state, proc)
        decreases(su(dec), dec)
      else True

    (And(su(pre), dec), vars_, phi_, rename)

  // for all values of the history h
  def havoc(h: Var, phi: Expr): Expr =
    val (hs, su) = Subst.rename(List(h))
    All(hs, su(phi))

  // the assumption and the commitment of procedure `name` for the arguments `args`, true if there are none
  def ac(state: State, name: Name, args: List[Expr]): (Expr, Expr) =
    val Proc(_, _, in, _) = state.procs(name)
    val attrs = state.procattrs(name)
    // the formal parameters are replaced and the type parameters instantiated by the arguments
    val su = Ref(Subst.empty[Type, Expr])
    Type.bind(state, in, args, su)
    (su(attrs.assumes), su(attrs.commits))

  // parallel composition of calls by the assumption-commitment contracts of the procedures over the history h,
  // inside of the procedure `proc` with the assumption `assume` and the commitment `commit`:
  // the commitments of the calls must hold for the history initially,
  // the assumption of `proc` and the commitments of the other calls must imply the assumption of each call,
  // and the commitments of the calls must imply the commitment of `proc`, both for all histories;
  // each call is a process that starts in the current state, which is verified modularly by its contract
  // like a call (see instance), i.e., its precondition must hold initially,
  // and afterwards, the results and modified variables of each call satisfy its postcondition,
  // where its history is a copy of its own, since the other processes extend the history as well,
  // and the history is arbitrary, satisfying all commitments
  def par(state: State, gs: List[Var], proc: Name, assume: Expr, commit: Expr, calls: List[Call], post: Expr): Expr =
    val h = state.history
    val (assumes, commits) = calls.map(call => ac(state, call.proc, call.args)).unzip

    val init = And(commits)

    val side =
      for (assume_, i) <- assumes.zipWithIndex
      yield havoc(h, Imp(And(assume :: commits.patch(i, Nil, 1)), assume_))

    val guarantee = havoc(h, Imp(And(commits), commit))

    // the calls do not share modified variables other than the history, hence the renamings do not overlap
    val instances = calls.map(instance(state, proc, _))
    val pres = instances.map(_._1)
    val fresh = instances.flatMap(_._2)
    val phis = instances.map(_._3)
    val renamed = instances.map(_._4).foldLeft(Subst.empty[Nothing, Var])(_ ++ _)
    val rename = renamed - h
    val effect = All(fresh, havoc(h, Imp(And(phis ++ commits), rename(post))))

    And((init :: side) ++ pres ++ List(guarantee, effect))

  // differential cuts for the invariants in sequence, followed by differential weakening:
  // each invariant must hold initially, and its derivative must hold whenever the domain and the equations x' = e hold,
  // where the domain is strengthened by the invariants before it;
  // finally, the postcondition must follow from the domain for all values that xs may evolve to;
  // the derivatives of the invariants are those of formulas, (e <= f)' is e' <= f', which is left to the simplifier
  def ode(xs: List[Var], rhs: List[Expr], dom: Expr, invs: List[Expr], post: Expr): Expr =
    // the values of xs after the evolution, and in its course, are fresh
    val (xs_, su) = Subst.rename(xs)
    val dom_ = su(dom)

    invs match
      case Nil =>
        All(xs_, Imp(dom_, su(post)))

      case inv :: rest =>
        val dxs_ = xs_.map(_.primed)
        val evolve = And(dom_ :: Eq(dxs_, su(rhs)))
        val cut = All(xs_ ++ dxs_, Imp(evolve, Diff(xs_, su(inv))))
        And(List(inv, cut, ode(xs, rhs, And(dom, inv), rest, post)))

  // the tick of the history by the time that has passed in a differential equation, if the history is declared
  def tick(state: State, time: Var): Option[Call] =
    for h <- state.vars.get("history")
    yield Tick(List(h, time), List(h))

  // loops with a test, and nondeterministic iterations without test, which may be left at any iteration
  def loop(state: State, gs: List[Var], proc: Name, assume: Expr, commit: Expr, test: Option[Expr], body: Prog, attrs: Attrs, post: Expr, return_ : Expr): Expr =
    val inv = attrs.invariant
    // the body modifies the local variables that it assigns, and the global variables in the modifies clause of the loop,
    // which subsumes those that it assigns, that calls modify, and the history that differential equations tick (Type.check)
    val xs = (body.mod ++ attrs.modifies).toList.distinct

    // the measure must decrease from the start to the end of each iteration, i.e., also on continue,
    // its values at the start are the fresh variables ms, which are replaced by the measure afterwards
    val dec = attrs.decreases
    val ms = Expr.vars("m", dec.map(_.typ)).fresh
    val su = Subst.from(ms, dec)
    val iter = And(inv, decreases(dec, ms))

    val step_ = su(wp(state, gs, proc, assume, commit, body, iter, post, iter, return_))
    val (step, exit) = test match
      case Some(test) => (Imp(test, step_), Imp(Not(test), post))
      case None       => (step_, post)

    And(inv, All(xs, Imp(inv, And(step, exit))))
