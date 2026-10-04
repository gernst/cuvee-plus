package cuvee.verify

import util.Name
import util.Ref
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.core.Attrs

// constrained Horn clauses, where pre-/postconditions and the program points are uninterpreted predicates:
// each procedure p(in) returns (out) has predicates p_pre(in, gs) and p_post(in, gs_, out, gs),
// where gs are the global variables and gs_ their values at the entry of p,
// the program points in the body of p have predicates p_assign_1, p_call_2, ..., generated on the fly,
// whose formal parameters are the variables in scope, including the global variables;
// each statement contributes the transitions from the facts before it to the predicates after it,
// the annotations requires, ensures, invariant, and decreases, as well as assertions, are goals in the head of clauses
object Horn extends Transform:
  // the logic is HORN, which replaces the one given in the input,
  // or is set at the beginning, i.e., when nothing has been passed through so far;
  // at the end of the input, the clauses are checked for satisfiability
  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
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

    // the model of the predicates are the inferred invariants, if the clauses are satisfiable
    val check =
      if last == Done
      then List(CheckSat, GetModel)
      else Nil

    logic ++ cmds_ ++ check

  // a procedure is either declared or defined, never both (see State.declare),
  // therefore its predicates p_pre and p_post are declared exactly once;
  // every procedure is an entry point: requires ⇒ p_pre,
  // and the callers must establish the precondition: p_pre ⇒ requires
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

        val gs = state.globals
        val gs_ = gs.fresh
        val ensures_ = Old.elim(gs, gs_, ensures)
        val mod = attrs.modifies
        val frame = for (g, g_) <- gs zip gs_ if !mod.contains(g) yield Eq(g, g_)

        val clauses = Ref[List[Expr]](Nil)
        clause(in ++ gs, List(requires), App(pre, in ++ gs), clauses)
        clause(in ++ gs, List(App(pre, in ++ gs)), requires, clauses)
        clause(in ++ gs_ ++ out ++ gs, App(pre, in ++ gs_) :: ensures_ :: frame, App(post, in ++ gs_ ++ out ++ gs), clauses)

        decls ++ clauses.value.map(axiom)

      // the body starts from the precondition p_pre with the global variables gs at their values gs_ at the entry,
      // which are never modified, and leads to p_post; the postcondition is the goal of p_pre ∧ p_post;
      // gs_ are fresh copies of the global variables, which cannot clash with other names in the clauses
      case DefineProc(Proc(name, params, in, out), body, _) =>
        val (pre, post, decls) = declare(state, name)
        val (_, _, requires, ensures) = Verify.contract(state, name)

        val gs = state.globals
        val gs_ = gs.fresh
        val scope = in ++ gs_ ++ out ++ gs
        // old(e) refers to the values gs_ at the entry
        val body_ = Old.elim(gs, gs_, body)
        val ensures_ = Old.elim(gs, gs_, ensures)
        val decls_ = Ref[List[DeclareFun]](Nil)
        val clauses = Ref[List[Expr]](Nil)

        clause(in ++ gs, List(requires), App(pre, in ++ gs), clauses)
        clause(in ++ gs, List(App(pre, in ++ gs)), requires, clauses)

        // the outputs are unconstrained initially
        val entry = App(pre, in ++ gs_) :: Eq(gs, gs_)
        val exit = List(App(post, scope))
        wp(state, name, scope, List(body_), entry, exit, None, None, exit, decls_, clauses)

        clause(scope, List(App(pre, in ++ gs_), App(post, scope)), ensures_, clauses)

        decls ++ decls_.value ++ clauses.value.map(axiom)

      case _ =>
        List(cmd)

  // the predicates p_pre and p_post of procedure `name` together with their declarations,
  // Horn solvers do not support polymorphism, therefore procedures must not have type parameters
  def declare(state: State, name: Name): (Fun, Fun, List[DeclareFun]) =
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
    val gs = state.globals
    Fun(name.name + "_pre", params, in ++ gs, Sort.bool)

  def postcondition(state: State, name: Name): Fun =
    val Proc(_, params, in, out) = state.procs(name)
    val gs = state.globals
    Fun(name.name + "_post", params, in ++ entry(gs) ++ out ++ gs, Sort.bool)

  // the formal parameters of p_post for the values of the global variables at the entry of a procedure,
  // fixed such that p_post is the same function at all uses
  def entry(gs: List[Var]): List[Var] =
    Expr.vars("g", gs.types)

  // a fresh predicate for a program point in procedure `proc` with the variables in `scope` as formal parameters,
  // numbered by the predicates declared so far
  def predicate(proc: Name, what: String, scope: List[Var], decls: Ref[List[DeclareFun]]): Fun =
    val pred = Fun(proc.name + "_" + what + "_" + (decls.value.length + 1), Nil, scope, Sort.bool)
    decls := decls.value :+ DeclareFun(pred, Attrs.empty)
    pred

  // add the clause ∀ scope. assumptions ⇒ head, unless the head is trivial,
  // where only the variables of the scope that occur are quantified
  def clause(scope: List[Var], assumptions: List[Expr], head: Expr, clauses: Ref[List[Expr]]): Unit =
    if head != True
    then
      val phi = Imp(And(assumptions), head)
      clauses := clauses.value :+ All(scope.filter(phi.free), phi)

  // a clause for each of the heads
  def clauses(scope: List[Var], assumptions: List[Expr], heads: List[Expr], clauses: Ref[List[Expr]]): Unit =
    for head <- heads
    do clause(scope, assumptions, head, clauses)

  // the transitions of `progs` from the facts `pre` that hold before them to the heads for each way they terminate:
  // normally (`post`), by break, by continue, and by return, where break and continue are only available inside loops;
  // the heads of each way are formulas over the variables in scope at the corresponding statement,
  // e.g. the predicate after a loop applied to the variables in scope there,
  // which are a subset of those at a break inside of nested blocks, whose locals are therefore dropped;
  // each statement that assigns leads to a fresh predicate over the scope, which holds before the remaining statements
  def wp(
      state: State,
      proc: Name,
      scope: List[Var],
      progs: List[Prog],
      pre: List[Expr],
      post: List[Expr],
      break: Option[List[Expr]],
      continue: Option[List[Expr]],
      return_ : List[Expr],
      decls: Ref[List[DeclareFun]],
      clauses: Ref[List[Expr]]
  ): Unit =
    progs match
      case Nil =>
        this.clauses(scope, pre, post, clauses)

      // the statements after a jump are unreachable
      case Break :: rest =>
        break match
          case Some(heads) =>
            this.clauses(scope, pre, heads, clauses)

          case None =>
            Error.raise("break outside of a loop", proc)

      case Continue :: rest =>
        continue match
          case Some(heads) =>
            this.clauses(scope, pre, heads, clauses)

          case None =>
            Error.raise("continue outside of a loop", proc)

      case Return :: rest =>
        this.clauses(scope, pre, return_, clauses)

      // the goal pre ⇒ pre_, and pre ∧ post_[xs := xs_] ⇒ next(scope[xs := xs_]), where xs_ are the new values of xs
      case Spec(xs, pre_, post_) :: rest =>
        clause(scope, pre, pre_, clauses)

        val next = predicate(proc, "spec", scope, decls)
        val xs_ = xs.fresh
        val su = Subst.from(xs, xs_)
        clause(scope ++ xs_, pre :+ su(post_), App(next, su(scope)), clauses)
        wp(state, proc, scope, rest, List(App(next, scope)), post, break, continue, return_, decls, clauses)

      // pre ⇒ next(scope[xs := rhs]), where next is a fresh predicate over the scope
      case Assign(xs, rhs) :: rest =>
        val next = predicate(proc, "assign", scope, decls)
        val su = Subst.from(xs, rhs)
        clause(scope, pre, App(next, su(scope)), clauses)
        wp(state, proc, scope, rest, List(App(next, scope)), post, break, continue, return_, decls, clauses)

      // pre ⇒ name_pre(args, gs), which collects the states in which `name` is called,
      // and pre ∧ name_post(args, gs, res_, gs[mod := mod_]) ⇒ next(scope[res, mod := res_, mod_]),
      // where res_ are the results and mod_ the new values of the global variables modified by `name`
      case Call(name, args, res) :: rest =>
        val Proc(_, _, in, out) = state.procs(name)

        Error.report("wrong number of arguments or results in call", name, args, res):
          require(in.length == args.length && out.length == res.length)

        // results and modified global variables are fresh since `args` may refer to their old values
        val gs = state.globals
        val mod = state.procattrs(name).modifies
        val res_ = res.fresh
        val mod_ = mod.fresh
        val su = Subst.from(res ++ mod, res_ ++ mod_)
        val next = predicate(proc, "call", scope, decls)

        clause(scope, pre, App(precondition(state, name), args ++ gs), clauses)

        // recursive calls must decrease the measure, which refers to the inputs that are in scope
        if name == proc then
          val dec = Verify.measure(state, proc)
          val su_ = Subst.from(in, args)
          if dec.nonEmpty then
            clause(scope, pre, Verify.decreases(su_(dec), dec), clauses)

        clause(
          scope ++ res_ ++ mod_,
          pre :+ App(postcondition(state, name), args ++ gs ++ res_ ++ su(gs)),
          App(next, su(scope)),
          clauses
        )
        wp(state, proc, scope, rest, List(App(next, scope)), post, break, continue, return_, decls, clauses)

      // the statements inside the block range over the scope extended by the locals, which are unconstrained initially,
      // each way to leave the block leads to heads over the outer scope, which drops the locals;
      // the remaining statements continue from a fresh predicate after the block, if there are any
      case Block(locals, progs_) :: rest =>
        // locals may shadow variables in scope, therefore they are renamed apart
        val locals_ = locals.fresh
        val su = Subst.from(locals, locals_)
        val scope_ = scope ++ locals_

        join(state, proc, "block", scope, rest, post, break, continue, return_, decls, clauses): post_ =>
          wp(state, proc, scope_, su(progs_), pre, post_, break, continue, return_, decls, clauses)

      // all alternatives start from pre and lead to the join point or to `post`,
      // from which the remaining statements continue
      case Choice(progs_) :: rest =>
        join(state, proc, "join", scope, rest, post, break, continue, return_, decls, clauses): post_ =>
          for prog <- progs_ do
            wp(state, proc, scope, List(prog), pre, post_, break, continue, return_, decls, clauses)

      // the branches start from pre together with the test or its negation
      case If(test, left, right) :: rest =>
        join(state, proc, "join", scope, rest, post, break, continue, return_, decls, clauses): post_ =>
          wp(state, proc, scope, List(left), pre :+ test, post_, break, continue, return_, decls, clauses)
          wp(state, proc, scope, List(right), pre :+ Not(test), post_, break, continue, return_, decls, clauses)

      // the continuous evolution has no counterpart in Horn clauses over the program variables
      case (prog: Ode) :: rest =>
        Error.raise("differential equations not supported in Horn clauses", proc, prog)

      case (prog: Par) :: rest =>
        Error.raise("parallel composition not supported in Horn clauses", proc, prog)

      // pre ⇒ inv(scope), where inv is the invariant at the loop head, whose annotation is the goal of inv(scope);
      // the body starts from inv(scope) ∧ test ∧ ms = measure, where the fresh variables ms are the values of the measure
      // at the start of the iteration, the end of an iteration and continue lead back to inv and to the goal measure < ms,
      // break leads to the predicate after the loop, as does inv(scope) ∧ ¬test after the body;
      // nondeterministic iterations have no test, i.e., inv(scope) leads to both the body and the exit
      case (loop @ (_: While | _: Iter)) :: rest =>
        val (test, body, attrs) = (loop: @unchecked) match
          case While(test, body, attrs) => (List(test), body, attrs)
          case Iter(body, attrs)        => (Nil, body, attrs)

        val dec = attrs.decreases
        val ms = Expr.vars("m", dec.map(_.typ)).fresh
        val scope_ = scope ++ ms

        val inv = predicate(proc, "inv", scope, decls)
        val head = App(inv, scope)
        val iter = if dec.isEmpty then List(head) else List(head, Verify.decreases(dec, ms))

        clause(scope, pre, head, clauses)
        clause(scope, List(head), attrs.invariant, clauses)

        join(state, proc, "exit", scope, rest, post, break, continue, return_, decls, clauses): exit =>
          wp(state, proc, scope_, List(body), head :: test ++ Eq(ms, dec), iter, Some(exit), Some(iter), return_, decls, clauses)
          this.clauses(scope, head :: test.map(Not(_)), exit, clauses)

  // the heads after a statement whose ways to continue are added by `body`,
  // which is a fresh predicate if there are remaining statements, from which these continue, and `post` otherwise
  def join(
      state: State,
      proc: Name,
      what: String,
      scope: List[Var],
      rest: List[Prog],
      post: List[Expr],
      break: Option[List[Expr]],
      continue: Option[List[Expr]],
      return_ : List[Expr],
      decls: Ref[List[DeclareFun]],
      clauses: Ref[List[Expr]]
  )(body: List[Expr] => Unit): Unit =
    if rest.isEmpty
    then body(post)
    else
      val next = predicate(proc, what, scope, decls)
      body(List(App(next, scope)))
      wp(state, proc, scope, rest, List(App(next, scope)), post, break, continue, return_, decls, clauses)
