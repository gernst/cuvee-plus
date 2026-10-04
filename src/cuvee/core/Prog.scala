package cuvee.core

import util.Name
import cuvee.sexpr.Attrs

case class Proc(name: Name, params: List[Param], in: List[Var], out: List[Var]):
  def args = in.types
  def res = out.types

sealed trait Prog:
  // the variables that are assigned, which excludes the global variables modified by calls
  def mod: Set[Var]
  // the variables that are read or assigned, including those in attributes, e.g. loop invariants
  def free: Set[Var]

object Prog:
  def free(attrs: Attrs): Set[Var] =
    attrs.attrs.flatMap(_._2).collect { case expr: Expr => expr.free }.flatten.toSet

  // replace the subprograms for which `f` is defined, top-down, i.e., f is not applied inside its results
  def rewrite(prog: Prog, f: PartialFunction[Prog, Prog]): Prog =
    val r = (prog: Prog) => rewrite(prog, f)
    if f.isDefinedAt(prog)
    then f(prog)
    else
      prog match
        case Break | Continue | Return | _: Spec | _: Assign | _: Call | _: Ode => prog
        case Block(locals, progs)     => Block(locals, progs.map(r))
        case Choice(progs)            => Choice(progs.map(r))
        case If(test, left, right)    => If(test, r(left), r(right))
        case While(test, body, attrs) => While(test, r(body), attrs)
        case Iter(body, attrs)        => Iter(r(body), attrs)
        case Par(calls)               => prog

case object Break extends Prog:
  def mod = Set()
  def free = Set()

case object Continue extends Prog:
  def mod = Set()
  def free = Set()

case object Return extends Prog:
  def mod = Set()
  def free = Set()

case class Spec(xs: List[Var], pre: Expr, post: Expr) extends Prog:
  def mod = Set(xs*)
  def free = pre.free ++ post.free ++ xs

object Spec:
  def havoc(xs: List[Var]) =
    Spec(xs, True, True)

  def assume(phi: Expr) =
    Spec(Nil, True, phi)

  def assert(phi: Expr) =
    Spec(Nil, phi, True)

case class Assign(lhs: List[Var], rhs: List[Expr]) extends Prog:
  def mod = Set(lhs*)
  def free = rhs.free ++ lhs

case class Call(proc: Name, args: List[Expr], res: List[Var]) extends Prog:
  def mod = Set(res*)
  def free = args.free ++ res

case class Block(locals: List[Var], progs: List[Prog]) extends Prog:
  def mod = progs.mod -- locals
  def free = progs.flatMap(_.free).toSet -- locals

case class Choice(progs: List[Prog]) extends Prog:
  def mod = progs.mod
  def free = progs.flatMap(_.free).toSet

case class If(test: Expr, left: Prog, right: Prog) extends Prog:
  def mod = left.mod ++ right.mod
  def free = test.free ++ left.free ++ right.free

case class While(test: Expr, body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod
  def free = test.free ++ body.free ++ Prog.free(attrs)

// a loop with a nondeterministic number of iterations, while * { body },
// which corresponds to the repetition of hybrid programs in dL
case class Iter(body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod
  def free = body.free ++ Prog.free(attrs)

// a system of ordinary differential equations x' = e for x in xs and e in rhs,
// which evolves for some time within the domain `dom`, the evolution constraint,
// as the continuous evolution of hybrid programs in dL, {x' = e, y' = f & dom},
// the attributes are e.g. differential invariants, as the invariants of loops; xs must be on Real
case class Ode(xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs) extends Prog:
  def mod = Set(xs*)
  def free = rhs.free ++ dom.free ++ xs ++ Prog.free(attrs)

// parallel composition of calls to processes, i.e., procedures with assumption-commitment contracts
// over the global history of events in their attributes, "assumes" and "commits",
// where the history is extended by the procedures send and receive;
// the calls must not share the variables that they modify, other than the history;
// break and continue do not leave a process, and return is not allowed
case class Par(calls: List[Call]) extends Prog:
  def mod = calls.mod
  def free = calls.flatMap(_.free).toSet

object Par:
  // the global history of events, and the procedures that extend it
  val history = Name("history", None)
  val send = Name("send", None)
  val receive = Name("receive", None)

  // the attribute that marks procedures as processes
  val process = "process"

  // the variables modified by a call, including the global variables modified by the procedure,
  // except for the history, which the processes share
  def modifies(state: State, call: Call): Set[Var] =
    val Call(name, _, res) = call
    val mod = cuvee.verify.Verify.modifies(state.procattrs(name))
    (res ++ mod).toSet.filterNot(_.name == history)

  // the variables modified by one call and used by another
  def shared(state: State, calls: List[Call]): Set[Var] =
    val pairs =
      for
        (left, i) <- calls.zipWithIndex
        (right, j) <- calls.zipWithIndex
        if i != j
      yield modifies(state, left) intersect (right.free.filterNot(_.name == history) ++ modifies(state, right))

    pairs.flatten.toSet
