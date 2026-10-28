package cuvee.prove

import util.Name
import cuvee.Config
import cuvee.core._
import cuvee.verify.Path
import cuvee.verify.TEQ

// the simplification of procedures by symbolic execution, slice by slice, which keeps the structure of the program, its statements,
// assignments, and if-then-else, and simplifies the expressions in it under the facts known at their position;
// nothing that is known is forgotten:
//
// - the context speaks about choices only, fresh variables for the nondeterministic choices of the program: the
//   inputs at the entry (parameters, outputs, globals, and the locals of blocks, whose initial values are not
//   determined), havoc and the outputs of contracts, the variables modified by calls, the alternatives of a choice
//   where they differ, and the state at the head of a loop; choices never change, hence the facts over them hold
//   until the end of the procedure;
// - each program variable is bound to its current value, a term over the choices (see At.values): an assignment
//   replaces the binding and adds no fact, a branch with a test joins the values by ite;
// - an expression of the program is simplified as its value in the context, and written back over the program
//   variables in scope (see written), where its value is expressed by them; otherwise it stays as it is, such that the
//   program never mentions a choice
//
// a loop starts from fresh choices for the variables that it modifies, constrained by its invariants, and with -slice
// by its trace equation system, simplified and attached to the loop as an invariant (see head); the facts from
// before the loop hold in its body and after it, since they do not speak about these choices; after the loop the test
// is known not to hold where it is left normally, and the positions of its breaks join that exit (see leave)
object Slice:
  // a position in the procedure `proc`: the context of the facts over the choices, the values of the program variables
  // in scope over the choices, and the facts assumed since the entry of the procedure, whose suffixes are the facts of
  // the branches that a join combines (see join)
  case class At(proc: Name, ctx: Context, values: Map[Var, Expr], facts: List[Expr]):
    def assume(config: Config, state: State, phi: Expr): At =
      if phi == True
      then this
      else copy(ctx = Forward.assume(config, state, ctx, List(phi), Nil), facts = facts :+ phi)

    // fresh choices for `xs`
    def havoc(xs: Iterable[Var]): At =
      copy(values = values ++ xs.map(x => x -> x.fresh))

  // how a statement ends: normally at a position, unless it does not terminate normally, and by break and continue at
  // the positions of these jumps, which the enclosing loop takes; return leaves the procedure, which is not followed
  case class Exits(normal: Option[At], breaks: List[At], continues: List[At]):
    // the jumps of `that` as well, e.g. of the statements of a sequence
    def jumps(that: Exits): Exits =
      Exits(normal, breaks ++ that.breaks, continues ++ that.continues)

    def map(f: At => At): Exits =
      Exits(normal.map(f), breaks.map(f), continues.map(f))

  object Exits:
    def normal(at: At): Exits =
      Exits(Some(at), Nil, Nil)

  // the context of a procedure has the rewrite rules and forward lemmas of the input, with one number of steps for the
  // whole procedure, as a goal has (see Context.withRules), and no polarity, which expressions of programs do not have;
  // the inputs of the procedure are choices, also the outputs and the global variables of the body, whose initial
  // values are those of the caller; the precondition holds at the entry; the body stays a block
  def simplify(config: Config, state: State, rules: List[Rule], forward: List[Forward], cmd: DefineProc): DefineProc =
    val DefineProc(proc, body, attrs) = cmd
    val ctx = Context.empty(state).withRules(rules, config.steps).copy(forward = forward).neutral
    val entry = At(proc.name, ctx, Map(), Nil).havoc(proc.in ++ proc.out ++ body.free)
    val at = entry.assume(config, state, value(config, state, entry, state.annotated(attrs).requires))
    val (body_, _) = simplify(config, state, at, body)
    body_ match
      case _: Block => DefineProc(proc, body_, attrs)
      case _        => DefineProc(proc, Block(Nil, List(body_)), attrs)

  // the value of `expr` at `at`, simplified in its context; the ite of the values joined after branches are lifted out of the atoms of
  // formulas, whose cases are then decided each under its test, e.g. x < 0 is false after if (x < 0) { x := -x; }
  def value(config: Config, state: State, at: At, expr: Expr): Expr =
    val su = Subst(Map(), at.values)
    val expr_ = if expr.typ == Sort.bool then Normalize.lift(su(expr)) else su(expr)
    Simplify.simplify(config, state, at.ctx, expr_)

  // `value` over the choices at `at`, with its subterms replaced by the program variables in scope that hold them, of
  // several those of `preferred` first, then the smallest by name, e.g. x of x < 0 after x := a; literals are not
  // replaced by variables of the same value; binders are entered only if `binders`, since a program variable could be
  // captured there
  def back(at: At, preferred: Set[Var], binders: Boolean, value: Expr): Expr =
    // the map keeps the last pair of a value, hence the order: preferred last, and among them the smallest name last
    val order = Ordering.Tuple2(Ordering.Boolean, Ordering.String.reverse)
    val holders =
      (for (x, e) <- at.values.toList.sortBy((x, _) => (preferred contains x, x.name.toString))(using order)
       if !e.isInstanceOf[Lit] && e != True && e != False
       yield e -> x).toMap

    def replace(expr: Expr): Expr =
      expr match
        case _ if holders contains expr => holders(expr)
        case _: App                     => expr.map(replace)
        case _ if binders               => expr.map(replace)
        case _                          => expr

    replace(value)

  // `expr` of the program, whose value is `value`, written back over the program variables in scope (see back), if no
  // choice remains (choices are fresh, never program variables), otherwise `expr` as it is; binders are not entered
  def written(at: At, expr: Expr, value: Expr): Expr =
    val expr_ = back(at, expr.free, false, value)
    if expr_.free.subsetOf(at.values.keySet)
    then expr_
    else expr

  // the invariant `phi` over the choices at the head `at` of a loop, written over the program variables in scope (see
  // back), also below binders, which are those of trace equation systems, whose bound variables are fresh; the choices
  // that remain, e.g. the number of iterations and the values at the entry of the variables that the loop modifies,
  // are quantified existentially, which keeps it inductive, as the choices do not change from one iteration to the next
  def invariant(at: At, phi: Expr): Expr =
    val phi_ = back(at, Set(), true, phi)
    val choices = (phi_.free -- at.values.keySet).toList.sortBy(_.name.toString)
    if choices.isEmpty then phi_ else Ex(choices, phi_)

  // `expr` of the program, simplified at `at` and written back
  def simplify(config: Config, state: State, at: At, expr: Expr): Expr =
    written(at, expr, value(config, state, at, expr))

  // the simplified program and how it ends (see Exits);
  // unreachable statements are dropped, after a jump or an inconsistent context, the branch of a decided test, a loop
  // that is not entered, and so are those of a block that have no effect;
  // each kind of statement has its helper, which simplifies its parts at the positions where they are evaluated
  def simplify(config: Config, state: State, at: At, prog: Prog): (Prog, Exits) =
    prog match
      case Break | Continue | Return      => jump(config, state, at, prog)
      case Spec(xs, pre, post)            => spec(config, state, at, xs, pre, post)
      case Assign(xs, rhs)                => assign(config, state, at, xs, rhs)
      case Call(name, args, res, vars)    => call(config, state, at, name, args, res, vars)
      case Block(locals, progs, attrs)    => block(config, state, at, locals, progs, attrs)
      case Choice(progs)                  => choice(config, state, at, progs)
      case If(test, left, right)          => if_(config, state, at, test, left, right)
      case While(test, body, attrs)       => while_(config, state, at, test, body, attrs)
      case Iter(body, attrs)              => iter(config, state, at, body, attrs)
      case Ode(time, xs, rhs, dom, attrs) => ode(config, state, at, time, xs, rhs, dom, attrs)
      case Par(progs)                     => par(config, state, at, progs)

  // a jump does not terminate normally, the statements after it are unreachable; break and continue end at the
  // position of the jump, which the enclosing loop takes
  def jump(config: Config, state: State, at: At, prog: Prog): (Prog, Exits) =
    prog match
      case Break    => (prog, Exits(None, List(at), Nil))
      case Continue => (prog, Exits(None, Nil, List(at)))
      case _        => (prog, Exits(None, Nil, Nil))

  // the precondition is assumed once it is checked, as in VCGen
  def spec(config: Config, state: State, at: At, xs: List[Var], pre: Expr, post: Expr): (Prog, Exits) =
    val pre_ = simplify(config, state, at, pre)
    val checked = at.assume(config, state, value(config, state, at, pre))
    val after = checked.havoc(xs)
    val post_ = simplify(config, state, after, post)
    val spec = if xs.isEmpty && pre_ == True && post_ == True then Skip else Spec(xs, pre_, post_)
    (spec, Exits.normal(after.assume(config, state, value(config, state, after, post))))

  // the right-hand sides are evaluated before any variable is bound to its new value; an assignment of the current
  // value of a variable has no effect
  def assign(config: Config, state: State, at: At, xs: List[Var], rhs: List[Expr]): (Prog, Exits) =
    val values = rhs.map(value(config, state, at, _))
    val rhs_ = (rhs zip values).map((e, v) => written(at, e, v))
    val changed = (xs zip rhs_).filterNot((x, e) => x == e)
    val assign = if changed.isEmpty then Skip else Assign(changed.map(_._1), changed.map(_._2))
    (assign, Exits.normal(at.copy(values = at.values ++ (xs zip values))))

  // the results and the global variables that the procedure modifies are choices
  def call(config: Config, state: State, at: At, name: util.Name, args: List[Expr], res: List[Var], vars: List[Var]): (Prog, Exits) =
    val prog = Call(name, args.map(simplify(config, state, at, _)), res, vars)
    (prog, Exits.normal(at.havoc(prog.mod intersect at.values.keySet)))

  // the locals are choices, their initial values are not determined; a block of a single statement without locals
  // and attributes is that statement, e.g. the branch of a decided test
  def block(config: Config, state: State, at: At, locals: List[Var], progs: List[Prog], attrs: Attrs): (Prog, Exits) =
    val (progs_, exits) = sequence(config, state, at.havoc(locals), progs)
    val restored = exits.map(scoped(at, _, locals))
    progs_.filterNot(_ == Skip) match
      case List(prog) if locals.isEmpty && attrs == Attrs.empty => (prog, restored)
      case progs__                                              => (Block(locals, progs__, attrs), restored)

  // each alternative from the same position, whose jumps are those of all alternatives
  def choice(config: Config, state: State, at: At, progs: List[Prog]): (Prog, Exits) =
    val results = progs.map(simplify(config, state, at, _))
    val exits = results.map(_._2)
    val normal = merge(config, state, at, exits.flatMap(_.normal))
    (Choice(results.map(_._1)), Exits(normal, exits.flatMap(_.breaks), exits.flatMap(_.continues)))

  // a decided test selects its branch
  def if_(config: Config, state: State, at: At, test: Expr, left: Prog, right: Prog): (Prog, Exits) =
    val cond = value(config, state, at, test)
    cond match
      case True =>
        simplify(config, state, at, left)

      case False =>
        simplify(config, state, at, right)

      case _ =>
        val (left_, l) = simplify(config, state, at.assume(config, state, cond), left)
        val (right_, r) = simplify(config, state, at.assume(config, state, Context.not(cond)), right)
        (If(written(at, test, cond), left_, right_), Exits(join(config, state, at, cond, l.normal, r.normal), Nil, Nil).jumps(l).jumps(r))

  // a loop that is not entered has no effect, but its head is reached, where its invariants are checked, as VCGen does;
  // otherwise its attributes are kept, its invariants hold at the head, where its trace equation system is attached as
  // a further one with -slice (see head); it is left where the test does not hold and at the breaks of its body (see
  // leave), whose continues end an iteration

  def while_(config: Config, state: State, at: At, test: Expr, body: Prog, attrs: Attrs): (Prog, Exits) =
    if value(config, state, at, test) == False
    then spec(config, state, at, Nil, And(state.annotated(attrs).invariants), True)
    else
      val (head, attrs_) = this.head(config, state, at, Some(test), body, attrs)
      val cond = value(config, state, head, test)
      val (body_, exits) = simplify(config, state, head.assume(config, state, cond), body)
      val exit = if cond == True then None else Some(head.assume(config, state, Context.not(cond)))
      (While(written(head, test, cond), body_, attrs_), leave(config, state, head, Some(cond), exit, exits.breaks))

  def iter(config: Config, state: State, at: At, body: Prog, attrs: Attrs): (Prog, Exits) =
    val (head, attrs_) = this.head(config, state, at, None, body, attrs)
    val (body_, exits) = simplify(config, state, head, body)
    (Iter(body_, attrs_), leave(config, state, head, None, Some(head), exits.breaks))

  // the position after a loop with the test `cond` at its `head`, if it has one, where it is left at the `exit`, where
  // the test does not hold, and at the `breaks` of its body, where it does: the breaks are merged (see merge), and joined
  // with the exit by the test like the branches of an if (see join), such that a test after the loop is decided in each
  // case, e.g. whether a search found its key; a loop without test is left at the head as well, merged with the
  // breaks; none if it is never left; it ends normally, its jumps are its own
  def leave(config: Config, state: State, head: At, cond: Option[Expr], exit: Option[At], breaks: List[At]): Exits =
    val broken = merge(config, state, head, breaks)
    cond match
      case Some(cond) => Exits(join(config, state, head, Context.not(cond), exit, broken), Nil, Nil)
      case None       => Exits(merge(config, state, head, exit.toList ++ breaks), Nil, Nil)

  // not simplified, its effect is havoc of the variables that it evolves
  def ode(config: Config, state: State, at: At, time: Var, xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs): (Prog, Exits) =
    (Ode(time, xs, rhs, dom, attrs), Exits.normal(at.havoc(xs.toSet intersect at.values.keySet)))

  // not simplified, its effect is havoc of the variables that it modifies
  def par(config: Config, state: State, at: At, progs: List[Prog]): (Prog, Exits) =
    val prog = Par(progs)
    (prog, Exits.normal(at.havoc(prog.mod intersect at.values.keySet)))

  // the position at the head of a loop with test `test` and its attributes: the variables that the body modifies are
  // choices, constrained by the invariants of the loop, also those of its tags (see State.annotated), as VCGen assumes
  // them; they are checked elsewhere, since the attributes are kept;
  // with -slice, the values of the variables that the loop modifies are those after an arbitrary number of iterations
  // of its trace equation system (see TEQ.head), built from the values at the entry and simplified in the context
  // before the loop, where it is equivalent, which the head assumes and the loop gets as a further invariant, over the
  // program variables (see invariant)
  def head(config: Config, state: State, at: At, test: Option[Expr], body: Prog, attrs: Attrs): (At, Attrs) =
    val system =
      if config.slice
      then TEQ.head(config, state, at.proc, test, body, attrs, Path(Subst(Map(), at.values)))
      else None

    val (head, attrs_) =
      system match
        case Some((_, cur, teq)) =>
          val phi = Simplify.simplify(config, state, at.ctx, teq)
          val head = at.copy(values = at.values ++ (TEQ.modified(body, attrs) zip cur)).assume(config, state, phi)
          // the invariant over the program variables is simplified once more, at a positive position, where the
          // equations of its existential variables are eliminated, e.g. those of traces that nothing else reads, in a
          // context without the facts, which are over the choices
          val inv = Simplify.simplify(config, state, at.ctx.restricted(_ => false).copy(polarity = Some(true)), invariant(head, phi))
          (head, if inv == True then attrs else attrs ++ Attrs(List("invariant" -> Some(inv))))

        case None =>
          (at.havoc(body.mod intersect at.values.keySet), attrs)

    (head.assume(config, state, value(config, state, head, And(state.annotated(attrs).invariants))), attrs_)

  // the statements of a block in sequence, up to the first that does not terminate normally or after which the
  // context is inconsistent, e.g. assume false: the statements after it are unreachable; the jumps of all of them
  def sequence(config: Config, state: State, at: At, progs: List[Prog]): (List[Prog], Exits) =
    progs match
      case Nil =>
        (Nil, Exits.normal(at))

      case prog :: rest =>
        simplify(config, state, at, prog) match
          case (prog_, exits @ Exits(Some(after), _, _)) if after.ctx.inconsistent =>
            (List(prog_), exits.copy(normal = None))

          case (prog_, exits @ Exits(Some(after), _, _)) =>
            val (rest_, last) = sequence(config, state, after, rest)
            (prog_ :: rest_, last.jumps(exits))

          case (prog_, exits) =>
            (List(prog_), exits)

  // the locals of a block go out of scope at its end, where the variables of the same names outside are visible
  // again with the values that they had before the block, which the block cannot have changed
  def scoped(outer: At, inner: At, locals: List[Var]): At =
    val values = locals.foldLeft(inner.values)((values, x) => outer.values.get(x) match
      case Some(e) => values.updated(x, e)
      case None    => values - x
    )
    inner.copy(values = values)

  // the join after the branches of a test `cond`: the values that differ are joined by ite, the facts of the branches
  // by a disjunction, each with its case of the test, unless they are the cases only; the facts before the branches
  // hold in both
  def join(config: Config, state: State, before: At, cond: Expr, left: Option[At], right: Option[At]): Option[At] =
    (left, right) match
      case (Some(l), Some(r)) =>
        val values = before.values.keySet.map(x => x -> (if l.values(x) == r.values(x) then l.values(x) else Ite(cond, l.values(x), r.values(x)))).toMap
        val ls = l.facts.drop(before.facts.length)
        val rs = r.facts.drop(before.facts.length)
        val joined = before.copy(values = values)
        if ls.length <= 1 && rs.length <= 1
        then Some(joined)
        else Some(joined.assume(config, state, Or(And(ls), And(rs))))

      case (Some(l), None) =>
        Some(l)

      case (None, Some(r)) =>
        Some(r)

      case (None, None) =>
        None

  // the merge after the alternatives of a choice, which has no test: the values that differ become fresh choices,
  // which each alternative defines in its disjunct of the facts
  def merge(config: Config, state: State, before: At, afters: List[At]): Option[At] =
    afters match
      case Nil =>
        None

      case List(after) =>
        Some(after)

      case _ =>
        val differ = before.values.keySet.filter(x => afters.map(_.values(x)).distinct.length > 1).toList
        val joined = before.havoc(differ)
        val disjuncts =
          for after <- afters
          yield And(after.facts.drop(before.facts.length) ++ differ.map(x => Eq(joined.values(x), after.values(x))))
        Some(joined.copy(values = before.values.keySet.map(x => x -> (if differ contains x then joined.values(x) else afters.head.values(x))).toMap).assume(config, state, Or(disjuncts)))
