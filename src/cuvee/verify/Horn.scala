package cuvee.verify

import util.Name
import util.Ref
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.sexpr.Attrs

// constrained Horn clauses, where pre-/postconditions and the program points are uninterpreted predicates:
// each procedure p(in) returns (out) has predicates p_pre(in, gs) and p_post(in, gs_, out, gs),
// where gs are the global variables and gs_ their values at the entry of p,
// the program points in the body of p have predicates p_1, p_2, ..., generated on the fly,
// whose formal parameters are the variables in scope, including the global variables;
// each statement contributes the transition from the predicate before it to those after it,
// the annotations requires, ensures, and invariant become queries on these predicates
object Horn extends Transform:
  // the logic is HORN, which replaces the one given in the input,
  // or is set at the beginning, i.e., when nothing has been passed through so far;
  // at the end of the input, the clauses are checked for satisfiability
  def apply(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State): List[Cmd] =
    val cmds_ =
      for
        cmd <- cmds;
        cmd_ <- horn(state, cmd)
      yield cmd_

    val hasLogic = cmds.exists:
      case SetLogic(_) => true
      case _           => false

    val logic =
      if prefix.isEmpty && !hasLogic
      then List(SetLogic("HORN"))
      else Nil

    val check =
      if last == Done
      then List(CheckSat)
      else Nil

    logic ++ cmds_ ++ check

  // a procedure is either declared or defined, never both (see State.declare),
  // therefore its predicates p_pre and p_post are declared exactly once;
  // every procedure is an entry point: requires ⇒ p_pre,
  // and the callers must establish the precondition: p_pre ∧ ¬requires ⇒ false
  def horn(state: State, cmd: Cmd): List[Cmd] =
    cmd match
      case SetLogic(_) =>
        List(SetLogic("HORN"))

      // global variables become arguments of the predicates
      case DeclareVar(_, _) =>
        Nil

      // procedures without body are trusted: p_pre ∧ ensures ⇒ p_post,
      // where the global variables that are not modified keep their values
      case DeclareProc(Proc(name, params, in, out), attrs) =>
        val (pre, post, decls) = declare(state, name)
        val (_, _, requires, ensures) = Verify.contract(state, name)

        val gs = Verify.globals(state)
        val gs_ = Horn.entry(gs)
        val mod = Verify.modifies(attrs)
        val frame = for (g, g_) <- gs zip gs_ if !mod.contains(g) yield Eq(g, g_)

        val clauses = Ref[List[Expr]](Nil)
        clause(in ++ gs, List(requires), App(pre, in ++ gs), clauses)
        clause(in ++ gs, List(App(pre, in ++ gs), Not(requires)), False, clauses)
        clause(in ++ gs_ ++ out ++ gs, App(pre, in ++ gs_) :: ensures :: frame, App(post, in ++ gs_ ++ out ++ gs), clauses)

        decls ++ clauses.value.map(axiom)

      // the body leads from p_pre to p_post, the postcondition is the query p_pre ∧ p_post ∧ ¬ensures ⇒ false;
      // the body ranges over the values gs_ of the global variables at the entry, which are never modified
      case DefineProc(Proc(name, params, in, out), body, _) =>
        val (pre, post, decls) = declare(state, name)
        val (_, _, requires, ensures) = Verify.contract(state, name)

        val gs = Verify.globals(state)
        val gs_ = Horn.entry(gs)
        val scope = in ++ gs_ ++ out ++ gs
        val decls_ = Ref[List[DeclareFun]](Nil)
        val clauses = Ref[List[Expr]](Nil)

        // p_pre ranges over the inputs and the global variables only, the outputs are unconstrained initially
        val entry = predicate(name, scope, decls_)
        clause(in ++ out ++ gs, List(App(pre, in ++ gs)), App(entry, in ++ gs ++ out ++ gs), clauses)
        wp(state, name, scope, List(body), entry, post, None, None, post, decls_, clauses)

        clause(in ++ gs, List(requires), App(pre, in ++ gs), clauses)
        clause(in ++ gs, List(App(pre, in ++ gs), Not(requires)), False, clauses)
        clause(scope, List(App(pre, in ++ gs_), App(post, scope), Not(ensures)), False, clauses)

        decls ++ decls_.value ++ clauses.value.map(axiom)

      case _ =>
        List(cmd)

  // the predicates p_pre and p_post of procedure `name` together with their declarations,
  // Horn solvers do not support polymorphism, therefore procedures must not have type parameters
  def declare(state: State, name: Name): (Fun, Fun, List[DeclareFun]) =
    Error.report("polymorphic procedures are not supported in Horn clauses", name):
      require(state.procs(name).params.isEmpty)

    val pre = precondition(state, name)
    val post = postcondition(state, name)

    for pred <- List(pre, post) do
      Error.report("predicate already declared", pred.name):
        require(!state.funs.contains((pred.name, pred.arity)))

    (pre, post, List(DeclareFun(pre, Attrs.empty), DeclareFun(post, Attrs.empty)))

  def axiom(phi: Expr): Assert =
    Assert(Axiom, Nil, phi, Attrs.empty)

  // the predicates p_pre and p_post of procedure `name`,
  // whose formal parameters are the inputs and the global variables,
  // resp. the inputs, the global variables at the entry, the outputs, and the global variables at the exit
  def precondition(state: State, name: Name): Fun =
    val Proc(_, params, in, out) = state.procs(name)
    val gs = Verify.globals(state)
    Fun(name.name + "_pre", params, in ++ gs, Sort.bool)

  def postcondition(state: State, name: Name): Fun =
    val Proc(_, params, in, out) = state.procs(name)
    val gs = Verify.globals(state)
    Fun(name.name + "_post", params, in ++ entry(gs) ++ out ++ gs, Sort.bool)

  // the values of the global variables at the entry of a procedure, which are the formal parameters of p_post,
  // they need not be fresh since each clause is quantified separately
  def entry(gs: List[Var]): List[Var] =
    Expr.vars("g", gs.types)

  // a fresh predicate for a program point in procedure `proc` with the variables in `scope` as formal parameters,
  // numbered by the predicates declared so far
  def predicate(proc: Name, scope: List[Var], decls: Ref[List[DeclareFun]]): Fun =
    val pred = Fun(proc.name + "_" + (decls.value.length + 1), Nil, scope, Sort.bool)
    decls := decls.value :+ DeclareFun(pred, Attrs.empty)
    pred

  // a fresh predicate over `inner` that leads to `target` over `outer`, which drops the additional variables of `inner`
  def exit(proc: Name, inner: List[Var], outer: List[Var], target: Fun, decls: Ref[List[DeclareFun]], clauses: Ref[List[Expr]]): Fun =
    val pred = predicate(proc, inner, decls)
    clause(inner, List(App(pred, inner)), App(target, outer), clauses)
    pred

  // add the clause ∀ scope. assumptions ⇒ head
  def clause(scope: List[Var], assumptions: List[Expr], head: Expr, clauses: Ref[List[Expr]]): Unit =
    clauses := clauses.value :+ All(scope, Imp(And(assumptions), head))

  // the transitions of `progs` from `pre` to the predicates for each way a program can terminate:
  // normally, by break, by continue, and by return, where break and continue are only available inside loops;
  // the first statement leads from `pre` to a fresh predicate, which is the pre of the remaining statements
  def wp(
      state: State,
      proc: Name,
      scope: List[Var],
      progs: List[Prog],
      pre: Fun,
      post: Fun,
      break: Option[Fun],
      continue: Option[Fun],
      return_ : Fun,
      decls: Ref[List[DeclareFun]],
      clauses: Ref[List[Expr]]
  ): Unit =
    progs match
      case Nil =>
        clause(scope, List(App(pre, scope)), App(post, scope), clauses)

      // the statements after a jump are unreachable
      case Break :: rest =>
        break match
          case Some(break) =>
            clause(scope, List(App(pre, scope)), App(break, scope), clauses)

          case None =>
            Error.raise("break outside of a loop", proc)

      case Continue :: rest =>
        continue match
          case Some(continue) =>
            clause(scope, List(App(pre, scope)), App(continue, scope), clauses)

          case None =>
            Error.raise("continue outside of a loop", proc)

      case Return :: rest =>
        clause(scope, List(App(pre, scope)), App(return_, scope), clauses)

      // the query pre(scope) ∧ ¬pre_ ⇒ false
      // and pre(scope) ∧ post_[xs := xs_] ⇒ next(scope[xs := xs_]), where xs_ are the new values of xs
      case Spec(xs, pre_, post_) :: rest =>
        clause(scope, List(App(pre, scope), Not(pre_)), False, clauses)

        val next = predicate(proc, scope, decls)
        val xs_ = xs.fresh
        val su = Subst.from(xs, xs_)
        clause(scope ++ xs_, List(App(pre, scope), su(post_)), App(next, su(scope)), clauses)
        wp(state, proc, scope, rest, next, post, break, continue, return_, decls, clauses)

      // pre(scope) ⇒ next(scope[xs := rhs]), where next is a fresh predicate over the scope
      case Assign(xs, rhs) :: rest =>
        val next = predicate(proc, scope, decls)
        val su = Subst.from(xs, rhs)
        clause(scope, List(App(pre, scope)), App(next, su(scope)), clauses)
        wp(state, proc, scope, rest, next, post, break, continue, return_, decls, clauses)

      // pre(scope) ⇒ name_pre(args, gs), which collects the states in which `name` is called,
      // and pre(scope) ∧ name_post(args, gs, res_, gs[mod := mod_]) ⇒ next(scope[res, mod := res_, mod_]),
      // where res_ are the results and mod_ the new values of the global variables modified by `name`
      case Call(name, args, res) :: rest =>
        val Proc(_, _, in, out) = state.procs(name)

        Error.report("wrong number of arguments or results in call", name, args, res):
          require(in.length == args.length && out.length == res.length)

        // results and modified global variables are fresh since `args` may refer to their old values
        val gs = Verify.globals(state)
        val mod = Verify.modifies(state.procattrs(name))
        val res_ = res.fresh
        val mod_ = mod.fresh
        val su = Subst.from(res ++ mod, res_ ++ mod_)
        val next = predicate(proc, scope, decls)

        clause(scope, List(App(pre, scope)), App(precondition(state, name), args ++ gs), clauses)

        // recursive calls must decrease the measure, which refers to the inputs that are in scope
        if name == proc then
          val dec = Verify.measure(state, proc)
          val su_ = Subst.from(in, args)
          if dec.nonEmpty then
            clause(scope, List(App(pre, scope), Not(Verify.decreases(su_(dec), dec))), False, clauses)

        clause(
          scope ++ res_ ++ mod_,
          List(App(pre, scope), App(postcondition(state, name), args ++ gs ++ res_ ++ su(gs))),
          App(next, su(scope)),
          clauses
        )
        wp(state, proc, scope, rest, next, post, break, continue, return_, decls, clauses)

      // the predicates inside the block range over the scope extended by the locals,
      // entering the block leaves the locals unconstrained,
      // each way to leave the block drops them again
      case Block(locals, progs_) :: rest =>
        // locals may shadow variables in scope, therefore they are renamed apart
        val locals_ = locals.fresh
        val su = Subst.from(locals, locals_)
        val scope_ = scope ++ locals_

        def exit(target: Fun): Fun =
          Horn.exit(proc, scope_, scope, target, decls, clauses)

        val entry = predicate(proc, scope_, decls)
        val next = predicate(proc, scope, decls)

        clause(scope_, List(App(pre, scope)), App(entry, scope_), clauses)
        wp(state, proc, scope_, su(progs_), entry, exit(next), break.map(exit), continue.map(exit), exit(return_), decls, clauses)
        wp(state, proc, scope, rest, next, post, break, continue, return_, decls, clauses)

      // all alternatives start from pre and lead to the join point,
      // from which the remaining statements continue
      case Choice(progs_) :: rest =>
        val join = predicate(proc, scope, decls)

        for prog <- progs_ do
          wp(state, proc, scope, List(prog), pre, join, break, continue, return_, decls, clauses)
        wp(state, proc, scope, rest, join, post, break, continue, return_, decls, clauses)

      // pre(scope) ∧ test ⇒ then(scope) and pre(scope) ∧ ¬test ⇒ else(scope),
      // both branches lead to the join point, from which the remaining statements continue
      case If(test, left, right) :: rest =>
        val then_ = predicate(proc, scope, decls)
        val else_ = predicate(proc, scope, decls)
        val join = predicate(proc, scope, decls)

        clause(scope, List(App(pre, scope), test), App(then_, scope), clauses)
        clause(scope, List(App(pre, scope), Not(test)), App(else_, scope), clauses)
        wp(state, proc, scope, List(left), then_, join, break, continue, return_, decls, clauses)
        wp(state, proc, scope, List(right), else_, join, break, continue, return_, decls, clauses)
        wp(state, proc, scope, rest, join, post, break, continue, return_, decls, clauses)

      // pre(scope) ⇒ inv(scope), where inv is the invariant at the loop head,
      // inv(scope) ∧ test ⇒ body(scope, measure), from which the body leads back to inv,
      // inv(scope) ∧ ¬test ⇒ next(scope), from which the remaining statements continue,
      // break leads to next, continue to inv,
      // and the annotated invariant is the query inv(scope) ∧ ¬invariant ⇒ false;
      // the body ranges over the scope extended by fresh variables ms for the values of the measure at the start of the iteration,
      // which are dropped on each way out of the body, where the end of an iteration is the query iter(scope, ms) ∧ ¬(measure < ms) ⇒ false
      case While(test, body, attrs) :: rest =>
        val dec = attrs.values[Expr]("decreases")
        val ms = Expr.vars("m", dec.map(_.typ)).fresh
        val scope_ = scope ++ ms

        def exit(target: Fun): Fun =
          Horn.exit(proc, scope_, scope, target, decls, clauses)

        val inv = predicate(proc, scope, decls)
        val body_ = predicate(proc, scope_, decls)
        val next = predicate(proc, scope, decls)
        val iter = exit(inv)
        val invariant = And(attrs.values[Expr]("invariant"))

        clause(scope, List(App(pre, scope)), App(inv, scope), clauses)
        clause(scope, List(App(inv, scope), test), App(body_, scope ++ dec), clauses)
        clause(scope, List(App(inv, scope), Not(test)), App(next, scope), clauses)
        clause(scope, List(App(inv, scope), Not(invariant)), False, clauses)
        if dec.nonEmpty then
          clause(scope_, List(App(iter, scope_), Not(Verify.decreases(dec, ms))), False, clauses)
        wp(state, proc, scope_, List(body), body_, iter, Some(exit(next)), Some(iter), exit(return_), decls, clauses)
        wp(state, proc, scope, rest, next, post, break, continue, return_, decls, clauses)
