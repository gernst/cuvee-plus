package cuvee.verify

import util.Name
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

        // the body may assume the assumption initially, its commitment is checked at send and receive (see wp)
        val (assume, _) = ac(state, name, in)
        val pre = And(pre_, assume)

        val body_ = Old.elim(gs, gs_, body)
        val post_ = Old.elim(gs, gs_, post)
        val phi = wp(state, gs, name, body_, post_, False, False, post_)
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
  // `proc` is the procedure that contains the program, whose recursive calls must decrease its measure
  def wp(state: State, gs: List[Var], proc: Name, progs: List[Prog], post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
    progs.foldRight(post):
      case (prog, phi) =>
        wp(state, gs, proc, prog, phi, break, continue, return_)

  def wp(state: State, gs: List[Var], proc: Name, prog: Prog, post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
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

      // send and receive assert the commitment of the enclosing procedure for the extended history
      // and assume it afterwards, i.e., the commitment must hold in addition to `post` after the call;
      // communication is joint, the event of a receive is that of the matching send of another process,
      // hence the commitment is made first also after receiving, since a commitment must always be made
      // before an assumption is taken, which is justified by the commitments of the other processes (see par)
      case Send(chan, value) =>
        committed(state, proc, Send(chan, value), post)

      case Recv(chan, x) =>
        committed(state, proc, Recv(chan, x), post)

      case call: Call =>
        this.call(state, proc, call, post)

      case Block(locals, progs) =>
        // locals may shadow variables in the postcondition, therefore they are renamed apart
        val locals_ = locals.fresh
        val su = Subst.from(locals, locals_)
        All(locals_, wp(state, gs, proc, su(progs), post, break, continue, return_))

      case Choice(progs) =>
        And(progs.map(wp(state, gs, proc, _, post, break, continue, return_)))

      case If(test, left, right) =>
        val left_ = Imp(test, wp(state, gs, proc, left, post, break, continue, return_))
        val right_ = Imp(Not(test), wp(state, gs, proc, right, post, break, continue, return_))
        And(left_, right_)

      case While(test, body, attrs) =>
        loop(state, gs, proc, Some(test), body, attrs, post, return_)

      case Iter(body, attrs) =>
        loop(state, gs, proc, None, body, attrs, post, return_)

      case Ode(xs, rhs, dom, attrs) =>
        ode(xs, rhs, dom, attrs.invariants, post)

      // the parallel composition extends the history like send and receive,
      // hence the commitment of the enclosing procedure is asserted and assumed afterwards as well
      case Par(calls) =>
        par(state, gs, proc, calls, And(commitment(state, proc), post))

  // the commitment of procedure `proc` for its own inputs
  def commitment(state: State, proc: Name): Expr =
    val (in, _, _, _) = contract(state, proc)
    val (_, commit) = ac(state, proc, in)
    commit

  def committed(state: State, proc: Name, call: Call, post: Expr): Expr =
    this.call(state, proc, call, And(commitment(state, proc), post))

  // calls by the contract of the procedure, where the measure of `proc` must decrease on recursive calls
  def call(state: State, proc: Name, call: Call, post: Expr): Expr =
    val Call(name, args, res) = call
    val (in, out, pre, phi) = contract(state, name)

    Error.report("wrong number of arguments or results in call", name, args, res):
      require(in.length == args.length && out.length == res.length)

    // results and the modified global variables are fresh since `args` may refer to their old values,
    // the precondition refers to the values of the global variables before the call,
    // as does old(e) in the postcondition, whose modified global variables are kept apart as mod0 meanwhile
    val mod = state.procattrs(name).modifies
    val res_ = res.fresh
    val mod_ = mod.fresh
    val mod0 = mod.fresh
    val su = Subst.from(in, args)
    val su_ = Subst.from(in ++ out ++ mod, args ++ res_ ++ mod_)
    val rename = Subst.from(res ++ mod, res_ ++ mod_)
    val phi_ = Subst.from(mod0, mod)(su_(Old.elim(mod, mod0, phi)))

    // the measure refers to the inputs, whose values at the call are those at the entry of `proc`
    val dec =
      if name == proc
      then
        val dec = measure(state, proc)
        decreases(su(dec), dec)
      else True

    And(List(su(pre), dec, All(res_ ++ mod_, Imp(phi_, rename(post)))))

  // the history of events, which must be declared as a global variable to use parallel composition
  def history(state: State): Var =
    Error.report("parallel composition requires a global variable history"):
      require(state.vars.contains(Par.history))

    state.vars(Par.history)

  // for all values of the history h
  def havoc(h: Var, phi: Expr): Expr =
    val h_ = h.fresh
    All(List(h_), Subst.from(List(h), List(h_))(phi))

  // the assumption and the commitment of procedure `name` for the arguments `args`, true if there are none
  def ac(state: State, name: Name, args: List[Expr]): (Expr, Expr) =
    val Proc(_, _, in, _) = state.procs(name)
    val attrs = state.procattrs(name)
    val su = Subst.from(in, args)
    (su(attrs.assumes), su(attrs.commits))

  // parallel composition of calls by the assumption-commitment contracts of the procedures over the history h:
  // the assumptions and commitments must hold for the history initially,
  // and the commitments of the other processes must imply the assumption of each process, for all histories;
  // since the calls do not share modified variables other than h, they can be verified in sequence,
  // where the history is arbitrary before each call, satisfying the assumption of the procedure,
  // and the history is arbitrary after the composition, satisfying all commitments
  def par(state: State, gs: List[Var], proc: Name, calls: List[Call], post: Expr): Expr =
    val h = history(state)
    val (assumes, commits) = calls.map(call => ac(state, call.proc, call.args)).unzip

    val init = And(assumes ++ commits)

    val side =
      for (assume, i) <- assumes.zipWithIndex
      yield havoc(h, Imp(And(commits.patch(i, Nil, 1)), assume))

    val last = havoc(h, Imp(And(commits), post))

    val seq = (calls zip assumes).foldRight(last):
      case ((call, assume), phi) =>
        havoc(h, Imp(assume, wp(state, gs, proc, call, phi, False, False, False)))

    And((init :: side) :+ seq)

  // differential cuts for the invariants in sequence, followed by differential weakening:
  // each invariant must hold initially, and its derivative must hold whenever the domain and the equations x' = e hold,
  // where the domain is strengthened by the invariants before it;
  // finally, the postcondition must follow from the domain for all values that xs may evolve to;
  // the derivatives of the invariants are those of formulas, (e <= f)' is e' <= f', which is left to the simplifier
  def ode(xs: List[Var], rhs: List[Expr], dom: Expr, invs: List[Expr], post: Expr): Expr =
    // the values of xs after the evolution, and in its course, are fresh
    val xs_ = xs.fresh
    val su = Subst.from(xs, xs_)
    val dom_ = su(dom)

    invs match
      case Nil =>
        All(xs_, Imp(dom_, su(post)))

      case inv :: rest =>
        val dxs_ = xs_.map(_.primed)
        val evolve = And(dom_ :: Eq(dxs_, su(rhs)))
        val cut = All(xs_ ++ dxs_, Imp(evolve, Diff(xs_, su(inv))))
        And(List(inv, cut, ode(xs, rhs, And(dom, inv), rest, post)))

  // the calls in a program, also inside of nested loops
  def calls(prog: Prog): List[Call] =
    prog match
      case call: Call => List(call)
      case _          => prog.subprogs.flatMap(this.calls)

  // loops with a test, and nondeterministic iterations without test, which may be left at any iteration
  def loop(state: State, gs: List[Var], proc: Name, test: Option[Expr], body: Prog, attrs: Attrs, post: Expr, return_ : Expr): Expr =
    val inv = attrs.invariant
    // calls in the body modify the global variables in the modifies attributes of the procedures they call,
    // and in the modifies attribute of the loop, if any
    val xs = (body.mod ++ attrs.modifies ++ calls(body).flatMap(call => state.procattrs(call.proc).modifies)).toList.distinct

    // the measure must decrease from the start to the end of each iteration, i.e., also on continue,
    // its values at the start are the fresh variables ms, which are replaced by the measure afterwards
    val dec = attrs.decreases
    val ms = Expr.vars("m", dec.map(_.typ)).fresh
    val su = Subst.from(ms, dec)
    val iter = And(inv, decreases(dec, ms))

    val step_ = su(wp(state, gs, proc, body, iter, post, iter, return_))
    val (step, exit) = test match
      case Some(test) => (Imp(test, step_), Imp(Not(test), post))
      case None       => (step_, post)

    And(inv, All(xs, Imp(inv, And(step, exit))))
