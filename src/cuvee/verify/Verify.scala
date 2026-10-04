package cuvee.verify

import util.Name
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.sexpr.Attrs

object Verify extends Transform:
  // the global variables gs are computed once and passed to the generation of the verification conditions
  def apply(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State): List[Cmd] =
    val gs = state.globals

    for
      cmd <- cmds;
      cmd_ <- verify(state, gs, cmd)
    yield cmd_

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
        val (in, out, pre, post) = contract(state, name)
        val gs_ = gs.fresh
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
    val pre = And(attrs.values[Expr]("requires"))
    val post = And(attrs.values[Expr]("ensures"))
    (in, out, pre, post)

  // the global variables in the modifies attributes of procedures and loops
  def modifies(attrs: Attrs): List[Var] =
    attrs.values[List[Var]]("modifies").flatten.distinct

  // the termination measure of procedure `name`, the components of a lexicographic order,
  // which is evaluated at the entry of the procedure, therefore it must refer to the inputs only,
  // which are never modified
  def measure(state: State, name: Name): List[Expr] =
    val Proc(_, _, in, _) = state.procs(name)
    val dec = state.procattrs(name).values[Expr]("decreases")

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

      case Call(name, args, res) =>
        val (in, out, pre, phi) = contract(state, name)

        Error.report("wrong number of arguments or results in call", name, args, res):
          require(in.length == args.length && out.length == res.length)

        // results and the modified global variables are fresh since `args` may refer to their old values,
        // the precondition refers to the values of the global variables before the call,
        // as does old(e) in the postcondition, whose modified global variables are kept apart as mod0 meanwhile
        val mod = modifies(state.procattrs(name))
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
        ode(xs, rhs, dom, attrs.values[Expr]("invariant"), post)

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

  // loops with a test, and nondeterministic iterations without test, which may be left at any iteration
  def loop(state: State, gs: List[Var], proc: Name, test: Option[Expr], body: Prog, attrs: Attrs, post: Expr, return_ : Expr): Expr =
    val inv = And(attrs.values[Expr]("invariant"))
    // calls in the body modify the global variables in the modifies attribute of the loop
    val xs = (body.mod ++ modifies(attrs)).toList

    // the measure must decrease from the start to the end of each iteration, i.e., also on continue,
    // its values at the start are the fresh variables ms, which are replaced by the measure afterwards
    val dec = attrs.values[Expr]("decreases")
    val ms = Expr.vars("m", dec.map(_.typ)).fresh
    val su = Subst.from(ms, dec)
    val iter = And(inv, decreases(dec, ms))

    val step_ = su(wp(state, gs, proc, body, iter, post, iter, return_))
    val (step, exit) = test match
      case Some(test) => (Imp(test, step_), Imp(Not(test), post))
      case None       => (step_, post)

    And(inv, All(xs, Imp(inv, And(step, exit))))
