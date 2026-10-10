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
// the variables of traces and lists bound on the positive chain ∀ xs. φ ⇒ ψ of a goal are uninterpreted constants,
// whose equations X == trace(...) are replaced by their characterization, other combinators are named by fresh
// functions of their free variables, defined in the antecedent of the goal, and the remaining functions of
// trace equation systems by fresh functions without definition, which generalizes the goal;
// functions defined with {:fold} are unfolded first; the declarations and lemmas of teq.dfy are dropped,
// as are lemmas over traces, lists, and naturals; guards need not be complete (see break), hence each case is
// an implication, and the entry is unconstrained if no guard holds
object Fallback extends Transform:
  // what lowering a goal has produced: the declarations of the new functions, their definitions as facts of the goal,
  // the applications of the new functions, without the index, that replace combinators and other sequences
  // with their lengths, and the applications that generalize other terms
  case class Lowered(decls: List[Cmd], defs: List[Expr], named: Map[Expr, (App, Expr)], general: Map[Expr, App])

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
        val out = Ref(Lowered(Nil, Nil, Map(), Map()))
        val phi_ = goal(state, Map(), out, phi)
        val Lowered(decls, defs, _, _) = out.value
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

  // the equations X == rhs of the antecedents along the chain of implications of `phi`
  def equations(phi: Expr): List[(Var, Expr)] =
    phi match
      case Imp(ante, concl) =>
        val eqs =
          And.flatten(ante).collect:
            case Eq(x: Var, rhs) if isSeq(x.typ) => (x, rhs)
            case Eq(rhs, x: Var) if isSeq(x.typ) => (x, rhs)
        eqs ++ equations(concl)

      case _ =>
        Nil

  // the dependencies of the iteration constraints of the antecedents along the chain of implications of `phi`
  def invariants(phi: Expr): List[List[Expr]] =
    phi match
      case Imp(ante, concl) =>
        val deps =
          And.flatten(ante).collect:
            case Invs(deps, _, _) => deps
        deps ++ invariants(concl)

      case _ =>
        Nil

  // the positive chain of a goal: the traces and lists bound by its universal quantifiers become constants
  def goal(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], phi: Expr): Expr =
    phi match
      case All(xs, body) =>
        val (seqs, rest) = xs.partition(x => isSeq(x.typ))
        val env_ = constants(state, env, out, seqs, equations(body), invariants(body))
        val nats = rest.filter(_.typ == Sort.nat)
        val body_ = goal(state, env_, out, body)
        All(rest.map(lower), if nats.isEmpty then body_ else Imp(And(nats.map(nonnegative)), body_))

      case Imp(ante, concl) =>
        val ante_ = And.flatten(ante).flatMap(premise(state, env, out, _))
        Imp(And(ante_), goal(state, env, out, concl))

      case And(phis) if phis.length > 1 =>
        And(phis.map(goal(state, env, out, _)))

      case _ =>
        expr(state, env, out, phi)

  // the uninterpreted constants for the traces and lists `seqs`, whose lengths are those of the first dependencies of
  // their equations, also for the lists among the dependencies of these and of the iteration constraints `invs`,
  // counters are kept
  def constants(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], seqs: List[Var], eqs: List[(Var, Expr)], invs: List[List[Expr]]): Map[Var, (Expr, Expr)] =
    val heads =
      for x <- seqs
      yield
        // goals of -split share their variables, hence a fresh index
        val fun = Fun(x.fresh.name, Nil, Expr.vars("x", List(Sort.int)), elem(x.typ))
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
    do out.map(o => o.copy(decls = DeclareFun(head.fun, Attrs.empty) :: o.decls))

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
        val su = Subst.from(acc :: bound, at(head, j) :: deps.map(entry(state, env, out, _, j)))
        val update_ = su(expr(state, env, out, update))
        val init_ = expr(state, env, out, init)
        And(Eq(at(head, Ints.zero), init_), All(List(j), Imp(range, cases(at(head, Ints.succ(j)), update_))))

      case Maps(deps, bound, update) =>
        val su = Subst.from(bound, deps.map(entry(state, env, out, _, j)))
        val update_ = su(expr(state, env, out, update))
        All(List(j), Imp(range, cases(at(head, j), update_)))

      case App(fun, inst, _, args) if isFold(state, fun) =>
        define(state, env, out, head, len, unfold(state, fun, inst, args))

      case _ =>
        Error.raise("not a combinator", rhs)

  // the conjuncts of an antecedent, where equations of constants are replaced by their characterization
  def premise(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], phi: Expr): List[Expr] =
    phi match
      case Eq(x: Var, rhs) if env.contains(x) && isSeq(x.typ) =>
        equation(state, env, out, x, rhs)

      case Eq(rhs, x: Var) if env.contains(x) && isSeq(x.typ) =>
        equation(state, env, out, x, rhs)

      case _ =>
        List(expr(state, env, out, phi))

  def equation(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], x: Var, rhs: Expr): List[Expr] =
    val (head, len) = env(x)
    (head, rhs) match
      // the counter is inlined
      case (Counter(_, _, _), Counter(_, _, _)) =>
        Nil

      case _ if dependencies(state, rhs).nonEmpty =>
        List(define(state, env, out, head, len, rhs))

      case _ =>
        List(expr(state, env, out, Eq(x, rhs)))

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

  def expr(state: State, env: Map[Var, (Expr, Expr)], out: Ref[Lowered], e: Expr): Expr =
    e match
      case x: Var =>
        lower(x)

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

      case Invs(deps, bound, body) =>
        val j = Var("j", Sort.int).fresh
        val (_, len) = sequence(state, env, out, deps.head)
        val su = Subst.from(bound, deps.map(entry(state, env, out, _, j)))
        val body_ = su(expr(state, env, out, body))
        All(List(j), Imp(And(Ints.le(Ints.zero, j), Ints.lt(j, len)), body_))

      case Bind(quant, xs, body) if xs.exists(_.typ == Sort.nat) =>
        val nats = And(xs.filter(_.typ == Sort.nat).map(nonnegative))
        val body_ = expr(state, env, out, body)
        val body__ = if quant == All.name then Imp(nats, body_) else And(nats, body_)
        Bind(quant, xs.map(lower), body__)

      // equations and other functions of traces, lists, and naturals are generalized
      case App(fun, _, typ, args) if isTeq(state, fun) || (typ :: args.types).exists(_.cons.exists(sorts.contains)) =>
        general(state, env, out, e)

      case _ =>
        e.map(expr(state, env, out, _))
