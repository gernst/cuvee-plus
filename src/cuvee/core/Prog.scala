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

// parallel composition of calls to procedures, whose assumption-commitment contracts
// over the shared history of events `history`, a global variable, are in their attributes, "assumes" and "commits";
// the calls must not share the variables that they modify, other than the history
case class Par(history: Var, calls: List[Call]) extends Prog:
  def mod = calls.mod
  def free = calls.flatMap(_.free).toSet + history

object Par:
  // the default name of the history in the frontends, which is extended by Send and Recv
  val history = Name("history", None)

  // the variables modified by a call, including the global variables modified by the procedure,
  // except for the history `h`
  def modifies(state: State, h: Var, call: Call): Set[Var] =
    val Call(name, _, res) = call
    val mod = cuvee.verify.Verify.modifies(state.procattrs(name))
    (res ++ mod).toSet - h

  // the variables modified by one call and used by another, other than the history `h`
  def shared(state: State, h: Var, calls: List[Call]): Set[Var] =
    val pairs =
      for
        (left, i) <- calls.zipWithIndex
        (right, j) <- calls.zipWithIndex
        if i != j
      yield modifies(state, h, left) intersect ((right.free - h) ++ modifies(state, h, right))

    pairs.flatten.toSet

// calls to the procedures send(c, v) and receive(c) returns (x), which extend the history by an event,
// where the enclosing procedure must keep its commitment
object Send:
  val name = Name("send", None)

  def apply(chan: Expr, value: Expr): Call =
    Call(name, List(chan, value), Nil)

  def unapply(prog: Prog): Option[(Expr, Expr)] =
    prog match
      case Call(`name`, List(chan, value), Nil) => Some((chan, value))
      case _                                    => None

object Recv:
  val name = Name("receive", None)

  def apply(chan: Expr, x: Var): Call =
    Call(name, List(chan), List(x))

  def unapply(prog: Prog): Option[(Expr, Var)] =
    prog match
      case Call(`name`, List(chan), List(x)) => Some((chan, x))
      case _                                 => None
