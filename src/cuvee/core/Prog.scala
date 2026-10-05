package cuvee.core

import util.Name

case class Proc(name: Name, params: List[Param], in: List[Var], out: List[Var]):
  def args = in.types
  def res = out.types

sealed trait Prog:
  // the variables that are assigned, which excludes the global variables modified by calls
  def mod: Set[Var]
  // the variables that are read or assigned, including those in attributes, e.g. loop invariants
  def free: Set[Var]

  // the immediate subprograms
  def subprogs: List[Prog] =
    this match
      case Block(_, progs)    => progs
      case Choice(progs)      => progs
      case If(_, left, right) => List(left, right)
      case While(_, body, _)  => List(body)
      case Iter(body, _)      => List(body)
      case Par(calls)         => calls
      case _                  => Nil

  // apply `e` to the immediate expressions, including those in attributes, and `p` to the immediate subprograms,
  // point-wise, where the assigned and local variables are kept
  def map(e: Expr => Expr, p: Prog => Prog): Prog =
    this match
      case Break | Continue | Return => this
      case Spec(xs, pre, post)       => Spec(xs, e(pre), e(post))
      case Assign(xs, rhs)           => Assign(xs, rhs.map(e))
      case Call(proc, args, res)     => Call(proc, args.map(e), res)
      case Block(locals, progs)      => Block(locals, progs.map(p))
      case Choice(progs)             => Choice(progs.map(p))
      case If(test, left, right)     => If(e(test), p(left), p(right))
      case While(test, body, attrs)  => While(e(test), p(body), attrs.map(e))
      case Iter(body, attrs)         => Iter(p(body), attrs.map(e))
      case Ode(xs, rhs, dom, attrs)  => Ode(xs, rhs.map(e), e(dom), attrs.map(e))
      case Par(calls)                => Par(for Call(proc, args, res) <- calls yield Call(proc, args.map(e), res))

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

object Choice extends (List[Prog] => Choice):
  // the alternatives of nested choices
  def flatten(progs: List[Prog]): List[Prog] =
    progs flatMap flatten

  def flatten(prog: Prog): List[Prog] =
    prog match
      case Choice(progs) => flatten(progs)
      case _             => List(prog)

case class If(test: Expr, left: Prog, right: Prog) extends Prog:
  def mod = left.mod ++ right.mod
  def free = test.free ++ left.free ++ right.free

case class While(test: Expr, body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod
  def free = test.free ++ body.free ++ attrs.free

// a loop with a nondeterministic number of iterations, while * { body },
// which corresponds to the repetition of hybrid programs in dL
case class Iter(body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod
  def free = body.free ++ attrs.free

// a system of ordinary differential equations x' = e for x in xs and e in rhs,
// which evolves for some time within the domain `dom`, the evolution constraint,
// as the continuous evolution of hybrid programs in dL, {x' = e, y' = f & dom},
// the attributes are e.g. differential invariants, as the invariants of loops; xs must be on Real
case class Ode(xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs) extends Prog:
  def mod = Set(xs*)
  def free = rhs.free ++ dom.free ++ xs ++ attrs.free

// parallel composition of calls to procedures, whose assumption-commitment contracts
// over the global history of events are in their attributes, "assumes" and "commits";
// the calls must not share the variables that they modify, other than the history
case class Par(calls: List[Call]) extends Prog:
  def mod = calls.mod
  def free = calls.flatMap(_.free).toSet

object Par:
  // the global history of events, which is extended by Send and Recv
  val history = Name("history", None)

  // the variables modified by a call, including the global variables modified by the procedure,
  // except for the history
  def modifies(state: State, call: Call): Set[Var] =
    val Call(name, _, res) = call
    val mod = state.procattrs(name).modifies
    (res ++ mod).toSet.filterNot(_.name == history)

  // the variables modified by one call and used by another, other than the history
  def shared(state: State, calls: List[Call]): Set[Var] =
    val pairs =
      for
        (left, i) <- calls.zipWithIndex
        (right, j) <- calls.zipWithIndex
        if i != j
      yield modifies(state, left) intersect (right.free.filterNot(_.name == history) ++ modifies(state, right))

    pairs.flatten.toSet

// calls h_ := h.send(c, v) and x, h_ := h.receive(c) of the methods of the type history (see hybrid.dfy),
// which return the history extended by an event, where the enclosing procedure must keep its commitment
object Send:
  val name = Name("history_send", None)

  def unapply(prog: Prog): Option[Call] =
    prog match
      case call @ Call(`name`, List(_, _, _), List(_)) => Some(call)
      case _                                         => None

object Recv:
  val name = Name("history_receive", None)

  def unapply(prog: Prog): Option[Call] =
    prog match
      case call @ Call(`name`, List(_, _), List(_, _)) => Some(call)
      case _                                         => None
