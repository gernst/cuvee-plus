package cuvee.transform

import util.SCC
import cuvee.Error
import cuvee.core._
import cuvee.verify.Path
import cuvee.verify.TEQ

// the trace equation system of a loop with its variables partitioned by the strongly connected components of their
// read relation (-teq-state, see ideas/deduction-engine-plan.md, section 1.2): a variable reads the variables that
// occur in its results and, if the paths are guarded, in the guards, which all components share; the components are
// ordered such that each comes after those it reads, and each becomes one trace, of a single accumulator for a
// variable that reads no other in a cycle (the per-variable form of the paper), of several accumulators for a cycle
// (core.Trace), with the counter, the histories of the earlier components that it reads and the choices as its
// dependencies; the exit values are current(X) and current(S).i, the iteration constraint ranges over the counter and
// all histories, ⌊X⌋ and ⌊S⌋.i; since the component graph is acyclic, no trace depends on another one, and the
// per-variable traces of a cycle are the projections of its trace (see prove.Views)
//
// the system of a nested loop is closed: the counter, the traces and the exit values are substituted by their
// definitions, in the order of the components, such that only the number of iterations and the choices are fresh at
// the exit and an inner loop is a value of the update of the outer one, not a family of fresh sequences; an outermost
// loop keeps its definitions as equations, which the engine follows on demand, so that the goal does not repeat the
// traces at every read
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
      p: Path,
      closed: Boolean
  ): (List[Var], List[Expr], Expr) =
    val index = sharp.zipWithIndex.toMap
    val results = for x <- xs yield TEQ.update(for q <- paths yield Upd(q.B, q(x)))
    val guards = paths.map(_.B).free.intersect(sharp.toSet)

    // the read relation: the loop variables (as x♯) in the result of a variable, and those of the guards if there are
    // several paths, whose guards every result has
    def reads(i: Int): Set[Int] =
      val own = results(i).free.intersect(sharp.toSet)
      (if paths.length > 1 then own ++ guards else own).map(index)

    val components = SCC(sharp.indices.toList, reads)

    // the trace of each component, its variable (named after the variable, capitalized, or S for a cycle), the
    // history of each loop variable as a dependency (⌊X⌋ or ⌊S⌋.i), and the exit values
    val traces = scala.collection.mutable.Map[Int, (Var, Trace)]()
    val histories = scala.collection.mutable.Map[Int, Expr]()
    val exits = scala.collection.mutable.Map[Int, Expr]()
    val order = scala.collection.mutable.ListBuffer[(Var, Trace)]()

    for component <- components
    do
      val accs = component.map(sharp)
      val inits = component.map(i => p(xs(i)))
      val results_ = component.map(results)
      val used = results_.free
      // the earlier components that this one reads, by their history and the bound variable x♯ of the read
      val earlier = sharp.indices.filter(j => !component.contains(j) && used.contains(sharp(j))).toList
      val choices = (zs zip Zs).filter((z, _) => used.contains(z))
      val deps = Butlast(K) :: earlier.map(histories) ++ choices.map(_._2)
      val bound = k :: earlier.map(sharp) ++ choices.map(_._1)
      val trace = Trace(inits, deps, accs, bound, results_)
      val variable =
        component match
          case List(i) => Var(xs(i).name.name.capitalize, trace.typ).fresh
          case _       => Var("S", trace.typ).fresh
      for (i, j) <- component.zipWithIndex
      do
        traces(i) = (variable, trace)
        histories(i) = if component.length == 1 then Butlast(variable) else History(variable, j)
        exits(i) = if component.length == 1 then Current(variable) else Component(variable, j)
      order += ((variable, trace))

    val counter = Counter(Ints.zero, Ints.one, n)
    val current = sharp.indices.map(exits).toList
    val iterations = Invs(Butlast(K) :: sharp.indices.map(histories).toList ++ Zs, k :: sharp ++ zs, constraint)
    val rest = List(iterations, Ints.le(Ints.zero, Nats.integer(n)))

    if closed
    then
      // the definitions refer to earlier ones only: the traces to the counter and the traces of earlier components,
      // the exit values to the traces; the substitution is composed in that order
      val su = order.foldLeft(Subst.from(List(K), List(counter)): Subst[Nothing, Expr]) { case (su, (x, trace)) => su + (x -> su(trace)) }
      (n :: Zs, current.map(su(_)), su(And(rest)))
    else
      val cur = xs.fresh
      val defs = Eq(K, counter) :: order.toList.map((x, trace) => Eq(x, trace)) ++ (cur zip current).map((x, e) => Eq(x, e))
      (cur ++ List(n, K) ++ order.map(_._1) ++ Zs, cur, And(defs ++ rest))
