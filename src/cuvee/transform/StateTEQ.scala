package cuvee.transform

import cuvee.Error
import cuvee.core._
import cuvee.verify.Path
import cuvee.verify.TEQ

// the trace equation system of a loop over its state (-teq-state, see ideas/state-trace.md and
// ideas/deduction-engine-implementation.md): the modified variables x₁, ..., xₘ form a tuple of the prelude of Dafny,
// tupleₘ(x₁, ..., xₘ), and the loop has a single trace S over it, whose update reads the variables as the components
// tupleₘ_i(s) of the accumulator s, and whose dependencies are the counter and the choices only, since the
// accumulator carries the state; the iteration constraint ranges over ⌊K⌋ and ⌊S⌋, since invs has no accumulator;
// the per-variable traces of the paper are the projections of S, which the engine of -prove follows on demand
// (see prove.Views); a loop with a single modified variable keeps its per-variable trace, closed in the same way
//
// the system is closed: since no trace depends on another one, the counter, the trace and the exit values of the loop
// are terms over the number of iterations and the choices, which are substituted, such that only those are fresh at
// the exit; an inner loop is then a value of the update of the outer one, not a family of fresh sequences
object StateTEQ:
  // the fresh variables of the exit, the exit values of the loop variables, and the system, like TEQ.system
  def system(
      state: State,
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
    val (s, st, trace, reads) =
      xs match
        // a loop with one modified variable keeps the per-variable form, which is its own projection
        case List(x) =>
          val x_ = sharp.head
          val X = Var(x.name.name.capitalize, Sort.trace(x.typ)).fresh
          val updates = for q <- paths yield Upd(q.B, q(x))
          val used = updates.free
          val choices = (zs zip Zs).filter((z, _) => used.contains(z))
          val trace = Trace(p(x), Butlast(K) :: choices.map(_._2), x_, k :: choices.map(_._1), TEQ.update(updates))
          (x_, X, trace, Subst.empty)

        case _ =>
          val m = xs.length
          Error.report("the tuple of the prelude of Dafny for the state of a loop is not declared", m):
            require(state.datatypes.contains(Tuples.name(m)))

          val Datatype(_, List((constr, sels))) = state.datatypes(Tuples.name(m)): @unchecked
          val sort = Sort(Con(Tuples.name(m), m), xs.types)
          val s = Var("s", sort).fresh
          val S = Var("S", Sort.trace(sort)).fresh

          // the loop variables x♯ of the paths are the components of the state s
          val reads = Subst.from(sharp, sels.map(sel => App(state, sel, List(s))))
          val updates = for q <- paths yield Upd(reads(q.B), reads(App(state, constr, xs.map(q(_)))))
          val used = updates.free
          val choices = (zs zip Zs).filter((z, _) => used.contains(z))
          val trace = Trace(App(state, constr, xs.map(p(_))), Butlast(K) :: choices.map(_._2), s, k :: choices.map(_._1), TEQ.update(updates))
          (s, S, trace, reads)

    // the definitions refer to each other in this order: the trace to the counter, the exit values to the trace
    val counter = Subst.from(List(K), List(Counter(Ints.zero, Ints.one, n)))
    val closed = counter + (st -> counter(trace))
    val cur =
      xs match
        case List(_) => List(closed(Current(st)))
        case _       => state.datatypes(Tuples.name(xs.length)).constrs.head._2.map(sel => closed(App(state, sel, List(Current(st)))))
    val iterations = Invs(Butlast(K) :: Butlast(st) :: Zs, k :: s :: zs, reads(constraint))

    (n :: Zs, cur, closed(And(List(iterations, Ints.le(Ints.zero, Nats.integer(n))))))
