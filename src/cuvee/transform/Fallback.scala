package cuvee.transform

import util.Name
import util.Ref
import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._

// the fallback encoding of trace equation systems into first-order logic (section 5.3 of the paper), for solvers:
// traces and lists of goals become uninterpreted functions of an integer index, whose entries are characterized
// point-wise, and naturals become integers; a trace X of n steps has the entries X(0), ..., X(n), its butlast those
// below n, and the length of all dependencies of a combinator is the n of its first one, ⌊counter(0, 1, n)⌋,
// written directly or by an equation K == counter(0, 1, n); counters are not named, their entries are i + j * c;
// the variables of traces and lists bound by universal quantifiers of positive polarity or by existential ones of
// negative polarity are uninterpreted functions, whose equations X == trace(...) among the hypotheses of the
// quantifier (see hypotheses) are replaced by their characterization; a list of traces, e.g. of an inner loop per
// iteration of the outer one, is a function of two indices with a function for the length of each trace, and a bound
// variable of a combinator that ranges over it is the trace of the current iteration; other combinators are named by
// fresh functions of their free variables, defined in the antecedent of the goal, and the remaining functions of
// trace equation systems by fresh functions without definition, which generalizes the goal;
// functions defined with {:fold} are unfolded first; the declarations and lemmas of teq.dfy are dropped,
// as are lemmas over traces, lists, and naturals; guards need not be complete (see break), hence each case is
// an implication, and the entry is unconstrained if no guard holds
object Fallback extends Transform:
  // what lowering a goal has produced: the declarations of the new functions, their definitions as facts of the goal,
  // the applications of the new functions, without the index, that replace combinators and other sequences
  // with their lengths, the applications that generalize other terms, and the functions for the lengths of the
  // traces of lists of traces
  case class Lowered(decls: List[Cmd], defs: List[Expr], named: Map[Expr, (App, Expr)], general: Map[Expr, App], inner: Map[Fun, Fun])

  // the sorts of trace equation systems
  val sorts = Set(Con.trace, Con.list, Con.nat)

  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    for
      cmd <- cmds
      cmd_ <- fallback(state, cmd)
    yield cmd_

  def fallback(state: State, cmd: Cmd): List[Cmd] =
    cmd match
      case Assert(Goal, Nil, phi, attrs) =>
        val out = Ref(Lowered(Nil, Nil, Map(), Map(), Map()))
        val phi_ = expr(state, Map(), out, phi, Some(true))
        val Lowered(decls, defs, _, _, _) = out.value
        val phi__ = if defs.isEmpty then phi_ else Imp(And(defs.reverse), phi_)
        decls.reverse :+ Assert(Goal, Nil, phi__, attrs)

      case Assert(Goal, _, _, _) =>
        Error.raise("polymorphic goals are not supported by -fallback", cmd)

      case decl: Decl if decl.attrs.contains("teq") =>
        Nil

      case Assert(_, _, All(xs, _), _) if xs.exists(x => x.typ.cons.exists(sorts.contains)) =>
        Nil

      case _ =>
        List(cmd)

  def isSeq(typ: Type) =
    typ match
      case Sort(Con.trace | Con.list, List(_)) => true
      case _                                   => false

  def elem(typ: Type) =
    typ match
      case Sort(Con.trace | Con.list, List(elem)) => elem
      case _                                      => Error.raise("not a trace or list", typ)

  // the type of the entries of nested traces and lists, with naturals as integers, and the number of indices
  def entries(typ: Type): (Type, Int) =
    typ match
      case Sort(Con.trace | Con.list, List(elem)) =>
        val (base, n) = entries(elem)
        (base, n + 1)

      case Sort.nat =>
        (Sort.int, 0)

      case _ =>
        (typ, 0)

  // the variable with naturals as integers
  def lower(x: Var) =
    if x.typ == Sort.nat then Var(x.name, Sort.int) else x

  def isFold(state: State, fun: Fun) =
    state.funattrs.get((fun.name, fun.arity)).exists(_.contains("fold"))

  def isTeq(state: State, fun: Fun) =
    state.funattrs.get((fun.name, fun.arity)).exists(_.contains("teq"))

  // the body of the function `fun` defined with {:fold} for the arguments `args`
  def unfold(state: State, fun: Fun, inst: List[Type], args: List[Expr]): Expr =
    val su = Type.bind(state, fun.args, inst)
    val body = state.fundefs((fun.name, fun.arity))
    // the formals are those of the declaration, before the types are instantiated
    su(Subst.from(fun.formals, args)(body))

  // the entry of a lowered trace or list `head`, a counter or the application of its function without the index, at `j`
  def at(head: Expr, j: Expr): Expr =
    head match
      case Counter(i, c, _) =>
        Ints.plus(i, Ints.times(j, c))

      case App(fun, inst, typ, args) =>
        App(fun, inst :+ Sort.int, typ, args :+ j)

      case _ =>
        Error.raise("not a lowered trace or list", head)

  def nonnegative(x: Var) =
    Ints.le(Ints.zero, lower(x))

  // the formulas that hold as hypotheses of all of `phi` of the polarity `positive`, as in the context of the
  // simplifier, from which the lengths of the traces and lists that `phi` binds follow, which must hold for all of
  // their occurrences: the antecedents of implications, the conjuncts of conjunctions that are hypotheses, and the
  // formulas of negative polarity of disjunctions, e.g. ¬(φ ∧ ψ) for the conclusion false is φ ∧ ψ ⇒ false;
  // not those of the conjuncts of a conjunction that is a goal, nor of the cases of implications and disjunctions
  // that are hypotheses, which hold only there, nor below quantifiers, whose variables they would refer to
  def hypotheses(phi: Expr, positive: Boolean): List[Expr] =
    phi match
      case Imp(ante, concl) if positive =>
        hypotheses(ante, false) ++ hypotheses(concl, true)

      case Not(arg) =>
        hypotheses(arg, !positive)

      case And(phis) if phis.length > 1 && !positive =>
        phis.flatMap(hypotheses(_, false))

      case Or(phis) if phis.length > 1 && positive =>
        phis.flatMap(hypotheses(_, true))

      case Imp(_, _) | And(_) | Or(_) | Bind(_, _, _) =>
        Nil

      case _ if !positive =>
        List(phi)

      case _ =>
        Nil

  // the equations X == rhs among the hypotheses
  def equations(hyps: List[Expr]): List[(Var, Expr)] =
    hyps.collect:
      case Eq(x: Var, rhs) if isSeq(x.typ) => (x, rhs)
      case Eq(rhs, x: Var) if isSeq(x.typ) => (x, rhs)

  // the dependencies of the iteration constraints among the hypotheses
  def invariants(hyps: List[Expr]): List[List[Expr]] =
    hyps.collect:
      case Invs(deps, _, _) => deps

  // the uninterpreted functions for the traces and lists `seqs`, whose lengths are those of the first dependencies of
  // their equations among the hypotheses `hyps`, also for the lists among the dependencies of these and of the
  // iteration constraints, counters are kept; lists of traces have a function for the length of each trace
  def constants(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], seqs: List[Var], hyps: List[Expr]): Map[Var, (Expr, Expr)] =
    val eqs = equations(hyps)
    val invs = invariants(hyps)

    val heads =
      for x <- seqs
      yield
        val (base, n) = entries(x.typ)
        Error.report("traces and lists nested more than twice are not supported by -fallback", x):
          require(n <= 2)
        // goals of -split share their variables, hence a fresh index
        val fun = Fun(x.fresh.name, Nil, Expr.vars("x", List.fill(n)(Sort.int)), base)
        x -> App(fun, Nil, fun.res, Nil)

    // counters are inlined
    val counters =
      eqs.collect:
        case (x, counter @ Counter(_, _, _)) if seqs.contains(x) =>
          x -> sequence(state, env, out, counter)

    // the lengths propagate along the equations until nothing changes
    def propagate(known: Map[Var, (Expr, Expr)]): Map[Var, (Expr, Expr)] =
      val found =
        for
          (x, rhs) <- eqs
          if seqs.contains(x) && !known.contains(x)
          n <- length(state, env ++ known, out, rhs)
        yield x -> n

      val deps =
        for
          (x, rhs) <- eqs
          if known.contains(x)
          dep <- dependencies(state, rhs)
          y <- dep match
            case Butlast(y: Var) => Some(y)
            case y: Var          => Some(y)
            case _               => None
          if seqs.contains(y) && !known.contains(y)
        yield y -> known(x)._2

      // the lists among the dependencies of an iteration constraint have the length of the others
      val iterations =
        for
          deps <- invs
          n <- deps.view.flatMap(length(state, env ++ known, out, _)).headOption.toList
          dep <- deps
          y <- dep match
            case Butlast(y: Var) => Some(y)
            case y: Var          => Some(y)
            case _               => None
          if seqs.contains(y) && !known.contains(y)
        yield y -> n

      val known_ = known ++ (found ++ deps ++ iterations).map((x, n) => x -> (heads.toMap.apply(x), n))
      if known_.size == known.size then known else propagate(known_)

    val known = propagate(counters.toMap)

    for x <- seqs if !known.contains(x)
    do Error.raise("the length of a trace or list is unknown to -fallback", x)

    for (x, head) <- heads if !counters.exists(_._1 == x)
    do
      out.map(o => o.copy(decls = DeclareFun(head.fun, Attrs.empty) :: o.decls))

      // the entries of lists of naturals are nonnegative
      if elem(x.typ) == Sort.nat then
        val is = Expr.vars("i", head.fun.args).fresh
        val phi = All(is, Ints.le(Ints.zero, App(head.fun, head.fun.args, head.fun.res, is)))
        out.map(o => o.copy(defs = phi :: o.defs))

      // the lengths of the traces of a list of traces, which are nonnegative
      if head.fun.arity == 2 then
        val lenfun = Fun(Name(head.fun.name.name + "_length", head.fun.name.index), Nil, Expr.vars("x", List(Sort.int)), Sort.int)
        val i = Var("i", Sort.int).fresh
        val phi = All(List(i), Ints.le(Ints.zero, App(lenfun, List(Sort.int), Sort.int, List(i))))
        out.map(o => o.copy(decls = DeclareFun(lenfun, Attrs.empty) :: o.decls, defs = phi :: o.defs, inner = o.inner + (head.fun -> lenfun)))

    env ++ known

  // the dependencies of a combinator or the unfolded application of a function defined with {:fold}
  def dependencies(state: State, rhs: Expr): List[Expr] =
    rhs match
      case Trace(_, deps, _, _, _)                    => deps
      case Maps(deps, _, _)                           => deps
      case App(fun, inst, _, args) if isFold(state, fun) => dependencies(state, unfold(state, fun, inst, args))
      case _                                          => Nil

  // the length of a trace (its number of steps) or of a list, if it is known
  def length(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], seq: Expr): Option[Expr] =
    seq match
      case x: Var if env.contains(x) =>
        Some(env(x)._2)

      case Butlast(t) =>
        length(state, env, out, t)

      case Counter(_, _, n) =>
        Some(expr(state, env, out, n))

      case Trace(_, deps, _, _, _) =>
        deps.view.flatMap(length(state, env, out, _)).headOption

      case Maps(deps, _, _) =>
        deps.view.flatMap(length(state, env, out, _)).headOption

      case App(fun, inst, _, args) if isFold(state, fun) =>
        length(state, env, out, unfold(state, fun, inst, args))

      case App(fun, _, _, List(n, _)) if fun.name.name == "consts" && isTeq(state, fun) =>
        Some(expr(state, env, out, n))

      case App(fun, _, _, List(k, xs)) if fun.name.name == "prefix" && isTeq(state, fun) =>
        Some(sequence(state, env, out, seq)._2)

      case _ =>
        out.value.named.get(seq).map(_._2)

  // the lowered trace or list `seq` and its length
  def sequence(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], seq: Expr): (Expr, Expr) =
    seq match
      case x: Var if env.contains(x) =>
        env(x)

      case Butlast(t) =>
        sequence(state, env, out, t)

      case Counter(i, c, n) =>
        val List(i_, c_, n_) = List(i, c, n).map(expr(state, env, out, _)): @unchecked
        (App(Fun.trace.counter, Nil, Sort.trace(Sort.int), List(i_, c_, n_)), n_)

      // the first k entries, or all of a shorter list
      case App(fun, _, _, List(k, xs)) if fun.name.name == "prefix" && isTeq(state, fun) =>
        val (head, len) = sequence(state, env, out, xs)
        val k_ = expr(state, env, out, k)
        (head, Ite(Ints.le(k_, len), k_, len))

      case _ =>
        named(state, env, out, seq)

  // the arguments of a fresh function for `e`: its free variables, where those of traces and lists are replaced by
  // the free variables of their lowered functions and lengths, e.g. the n of the counter K == counter(0, 1, n)
  // of a dependency ⌊K⌋, such that terms over traces of different lengths are distinct
  def arguments(env: Map[Var, (Expr, Expr)], e: Expr): List[Var] =
    val lowered = e.free.filter(env.contains).flatMap(x => env(x)._1.free ++ env(x)._2.free)
    (e.free.filterNot(env.contains).map(lower) ++ lowered).toList.sortBy(_.toString)

  // a fresh function of the free variables for a combinator, defined in the antecedent of the goal,
  // or for another trace or list, with a fresh function for its length, both without definition
  def named(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], seq: Expr): (App, Expr) =
    out.value.named.get(seq) match
      case Some(result) =>
        result

      case None =>
        val xs = arguments(env, seq)

        // the definitions hold for the arguments that are naturals, which are nonnegative
        val nats = And(seq.free.toList.filter(_.typ == Sort.nat).map(nonnegative))

        Error.report("trace or list with free sequences not supported by -fallback", seq):
          require(!xs.exists(x => x.typ.cons.exists(sorts.contains)))

        val index = Var.next()
        val name = seq match
          case _: Trace      => Name("trace", Some(index))
          case _: Maps       => Name("maps", Some(index))
          case App(fun, _, _, _) => Name(fun.name.name, Some(index))
          case _             => Name("seq", Some(index))

        val fun = Fun(name, Nil, Expr.vars("x", xs.types :+ Sort.int), elem(seq.typ))
        val head = App(fun, xs.types, fun.res, xs)
        val combinator = dependencies(state, seq).nonEmpty

        val consts = seq match
          case App(fun, _, _, List(n, _)) if fun.name.name == "consts" && isTeq(state, fun) => Some(expr(state, env, out, n))
          case _ => None

        val (len, decls) =
          if consts.nonEmpty then (consts.get, List(DeclareFun(fun, Attrs.empty)))
          else if combinator then
            val len = length(state, env, out, seq).getOrElse:
              Error.raise("the length of a combinator is unknown to -fallback", seq)
            (len, List(DeclareFun(fun, Attrs.empty)))
          else
            val lenfun = Fun(Name(name.name + "_length", Some(index)), Nil, Expr.vars("x", xs.types), Sort.int)
            (App(lenfun, xs.types, Sort.int, xs), List(DeclareFun(fun, Attrs.empty), DeclareFun(lenfun, Attrs.empty)))

        out.map(o => o.copy(decls = decls.reverse ++ o.decls, named = o.named + (seq -> (head, len))))

        seq match
          case App(fun, _, _, List(n, v)) if fun.name.name == "consts" && isTeq(state, fun) =>
            // all n + 1 entries are v
            val j = Var("j", Sort.int).fresh
            val v_ = expr(state, env, out, v)
            val range = And(Ints.le(Ints.zero, j), Ints.le(j, len))
            val phi = All(xs, Imp(nats, All(List(j), Imp(range, Eq(at(head, j), v_)))))
            out.map(o => o.copy(defs = phi :: o.defs))

          case _ if combinator =>
            val phi = All(xs, Imp(nats, define(state, env, out, head, len, seq)))
            out.map(o => o.copy(defs = phi :: o.defs))

          case _ =>
            val phi = All(xs, Ints.le(Ints.zero, len))
            out.map(o => o.copy(defs = phi :: o.defs))

        (head, len)

  // the entry of the dependency `dep` at `j`
  def entry(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], dep: Expr, j: Expr): Expr =
    val (head, _) = sequence(state, env, out, dep)
    at(head, j)

  // the bound variables of a combinator at the position `j` of its dependencies: those of traces and lists, which
  // range over a list of traces, are the trace at `j` with its length, the others are substituted by the entries
  def bind(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], deps: List[Expr], bound: List[Var], j: Expr): (Map[Var, (Expr, Expr)], Subst[Nothing, Expr]) =
    val (seqs, scalars) = (deps zip bound).partition((_, x) => isSeq(x.typ))

    val env_ =
      for (dep, x) <- seqs
      yield
        val (head, _) = sequence(state, env, out, dep)
        val lenfun = head match
          case App(fun, _, _, _) if out.value.inner.contains(fun) => out.value.inner(fun)
          case _ => Error.raise("traces that are not the entries of a list are not supported by -fallback", dep)
        val App(_, _, _, args) = head: @unchecked
        x -> (at(head, j), App(lenfun, (args :+ j).types, Sort.int, args :+ j))

    val su = Subst.from(scalars.map((_, x) => lower(x)), scalars.map((dep, _) => entry(state, env, out, dep, j)))
    (env ++ env_, su)

  // the case φ ⇒ lhs == e of each guarded result, or the equation of a single one
  def cases(lhs: Expr, update: Expr): Expr =
    update match
      case Eps(updates) => And(updates.map(upd => Imp(upd.cond, Eq(lhs, upd.rhs))))
      case _            => Eq(lhs, update)

  // the point-wise characterization of the trace or list `head` of length `len` given by the combinator `rhs`
  def define(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], head: Expr, len: Expr, rhs: Expr): Expr =
    val j = Var("j", Sort.int).fresh
    val range = And(Ints.le(Ints.zero, j), Ints.lt(j, len))

    rhs match
      case Trace(init, deps, acc, bound, update) =>
        val (env_, su) = bind(state, env, out, deps, bound, j)
        val update_ = Subst.from(List(lower(acc)), List(at(head, j)))(su(expr(state, env_, out, update)))
        val init_ = expr(state, env, out, init)
        And(Eq(at(head, Ints.zero), init_), All(List(j), Imp(range, cases(at(head, Ints.succ(j)), update_))))

      case Maps(deps, bound, update) =>
        val (env_, su) = bind(state, env, out, deps, bound, j)
        val update_ = su(expr(state, env_, out, update))
        All(List(j), Imp(range, cases(at(head, j), update_)))

      // the entries i + j * c of a counter, all n + 1 of them
      case Counter(i, c, _) =>
        val List(i_, c_) = List(i, c).map(expr(state, env, out, _)): @unchecked
        All(List(j), Imp(And(Ints.le(Ints.zero, j), Ints.le(j, len)), Eq(at(head, j), Ints.plus(i_, Ints.times(j, c_)))))

      case App(fun, inst, _, args) if isFold(state, fun) =>
        define(state, env, out, head, len, unfold(state, fun, inst, args))

      case _ =>
        Error.raise("not a combinator", rhs)

  // the characterization of an equation x == rhs of a trace or list x, with the length of x if it differs from that of
  // the dependencies of rhs, e.g. of the trace of a list of traces; an inlined counter needs none
  def equation(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], x: Var, rhs: Expr): Expr =
    val (head, len) = env(x)
    (head, rhs) match
      case (Counter(_, _, _), Counter(_, _, _)) =>
        True

      case _ if dependencies(state, rhs).nonEmpty || Counter.unapply(rhs).isDefined =>
        val len_ = length(state, env, out, rhs).getOrElse:
          Error.raise("the length of a combinator is unknown to -fallback", rhs)
        val phi = define(state, env, out, head, len, rhs)
        if len_ == len then phi else And(Eq(len, len_), phi)

      case _ =>
        general(state, env, out, Eq(x, rhs))

  // a fresh function of the free variables in place of `e`, which generalizes the goal
  def general(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], e: Expr): Expr =
    out.value.general.get(e) match
      case Some(app) =>
        app

      case None =>
        val xs = arguments(env, e)

        Error.report("term with free sequences not supported by -fallback", e):
          require(!xs.exists(x => x.typ.cons.exists(sorts.contains)))

        val name = e match
          case App(fun, _, _, _) => Name(fun.name.name, Some(Var.next()))
          case _                 => Name("general", Some(Var.next()))

        val typ = if e.typ == Sort.nat then Sort.int else e.typ
        val fun = Fun(name, Nil, Expr.vars("x", xs.types), typ)
        val app = App(fun, xs.types, typ, xs)
        out.map(o => o.copy(decls = DeclareFun(fun, Attrs.empty) :: o.decls, general = o.general + (e -> app)))
        app

  // the lowered formula or term `e`, whose polarity, if it is a formula, is `polarity`: the variables of traces and
  // lists of quantifiers that can be skolemized are uninterpreted functions, those of other quantifiers are errors
  def expr(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], e: Expr, polarity: Option[Boolean] = None): Expr =
    e match
      case x: Var =>
        lower(x)

      case Bind(quant, xs, body) if xs.exists(x => isSeq(x.typ)) =>
        val positive = polarity.getOrElse:
          Error.raise("traces and lists bound in a term are not supported by -fallback", e)

        Error.report("traces and lists bound by a quantifier that cannot be skolemized are not supported by -fallback", e):
          require(quant == (if positive then All.name else Ex.name))

        val (seqs, rest) = xs.partition(x => isSeq(x.typ))
        val env_ = constants(state, env, out, seqs, hypotheses(body, positive))
        if rest.isEmpty then expr(state, env_, out, body, polarity) else expr(state, env_, out, Bind(quant, rest, body), polarity)

      case Bind(quant, xs, body) =>
        val nats = And(xs.filter(_.typ == Sort.nat).map(nonnegative))
        val body_ = expr(state, env, out, body, polarity)
        val body__ = if nats == True then body_ else if quant == All.name then Imp(nats, body_) else And(nats, body_)
        Bind(quant, xs.map(lower), body__)

      case Imp(ante, concl) =>
        Imp(expr(state, env, out, ante, polarity.map(!_)), expr(state, env, out, concl, polarity))

      case Not(arg) =>
        Not(expr(state, env, out, arg, polarity.map(!_)))

      // without the inlined equations of counters, which are true
      case And(phis) if phis.length > 1 =>
        And(phis.map(expr(state, env, out, _, polarity)).conjuncts)

      case Or(phis) if phis.length > 1 =>
        Or(phis.map(expr(state, env, out, _, polarity)))

      case Eq(x: Var, rhs) if env.contains(x) && isSeq(x.typ) =>
        equation(state, env, out, x, rhs)

      case Eq(rhs, x: Var) if env.contains(x) && isSeq(x.typ) =>
        equation(state, env, out, x, rhs)

      case Current(t) =>
        val (head, len) = sequence(state, env, out, t)
        at(head, len)

      case Earlier(k, seq) =>
        entry(state, env, out, seq, expr(state, env, out, k))

      case Nats.integer(n) =>
        expr(state, env, out, n)

      case Nats.natural(x) =>
        val x_ = expr(state, env, out, x)
        Ite(Ints.le(Ints.zero, x_), x_, Ints.zero)

      case Nats.zero() =>
        Ints.zero

      case Nats.succ(n) =>
        Ints.succ(expr(state, env, out, n))

      case App(fun, _, _, List(seq)) if fun.name.name == "length" && isSeq(seq.typ) =>
        sequence(state, env, out, seq)._2

      // the body holds at each position of the dependencies, like that of a universal quantifier
      case Invs(deps, bound, body) =>
        val j = Var("j", Sort.int).fresh
        val (_, len) = sequence(state, env, out, deps.head)
        val (env_, su) = bind(state, env, out, deps, bound, j)
        val body_ = su(expr(state, env_, out, body, polarity))
        All(List(j), Imp(And(Ints.le(Ints.zero, j), Ints.lt(j, len)), body_))

      // equations and other functions of traces, lists, and naturals are generalized
      case App(fun, _, typ, args) if isTeq(state, fun) || (typ :: args.types).exists(_.cons.exists(sorts.contains)) =>
        general(state, env, out, e)

      case _ =>
        e.map(expr(state, env, out, _))
