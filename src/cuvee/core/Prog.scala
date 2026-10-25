package cuvee.core

import util.Name

case class Proc(name: Name, params: List[Param], in: List[Var], out: List[Var]):
  def args = in.types
  def res = out.types

sealed trait Prog:
  // the variables that are assigned, including the global variables modified by calls (see Call)
  def mod: Set[Var]
  // the variables that are read or assigned, including those in attributes, e.g. loop invariants
  def free: Set[Var]
  // the functions applied in the expressions, including those in attributes
  def funs: Set[Fun]
  // whether the program contains return
  def returns: Boolean
  // whether the program contains a loop without invariants, whose invariant is true
  def abstracts: Boolean
  // the procedures that the program calls
  def calls: Set[Name]

  // apply `e` to the immediate expressions, including those in attributes, and `p` to the immediate subprograms,
  // point-wise, where the assigned and local variables are kept
  def map(e: Expr => Expr, p: Prog => Prog): Prog =
    this match
      case Break | Continue | Return   => this
      case Spec(xs, pre, post)         => Spec(xs, e(pre), e(post))
      case Assign(xs, rhs)             => Assign(xs, rhs.map(e))
      case Call(proc, args, res, vars) => Call(proc, args.map(e), res, vars)
      case Block(locals, progs, attrs) => Block(locals, progs.map(p), attrs.map(e))
      case Choice(progs)               => Choice(progs.map(p))
      case If(test, left, right)       => If(e(test), p(left), p(right))
      case While(test, body, attrs)    => While(e(test), p(body), attrs.map(e))
      case Iter(body, attrs)           => Iter(p(body), attrs.map(e))
      case Ode(t, xs, rhs, dom, attrs) => Ode(t, xs, rhs.map(e), e(dom), attrs.map(e))
      case Par(progs)                  => Par(progs.map(p))

case object Break extends Prog:
  def mod = Set()
  def free = Set()
  def funs = Set()
  def returns = false
  def abstracts = false
  def calls = Set()

case object Continue extends Prog:
  def mod = Set()
  def free = Set()
  def funs = Set()
  def returns = false
  def abstracts = false
  def calls = Set()

case object Return extends Prog:
  def mod = Set()
  def free = Set()
  def funs = Set()
  def returns = true
  def abstracts = false
  def calls = Set()

case class Spec(xs: List[Var], pre: Expr, post: Expr) extends Prog:
  def mod = Set(xs*)
  def free = pre.free ++ post.free ++ xs
  def funs = pre.funs ++ post.funs
  def returns = false
  def abstracts = false
  def calls = Set()

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
  def funs = rhs.funs
  def returns = false
  def abstracts = false
  def calls = Set()

// `vars` are the global variables that the procedure modifies, its modifies clause in its order, which Type.check fills
// in when it resolves the call; the frontends build calls with none, as they build the arguments before their types
// are checked
case class Call(proc: Name, args: List[Expr], res: List[Var], vars: List[Var]) extends Prog:
  def mod = Set(res*) ++ vars
  def free = args.free ++ res ++ vars
  def funs = args.funs
  def returns = false
  def abstracts = false
  def calls = Set(proc)

// the attributes of a block are those of a statement of SV-LIB, (! (sequence ...) :tag t), e.g. location invariants,
// which State.annotated asserts at its beginning
case class Block(locals: List[Var], progs: List[Prog], attrs: Attrs = Attrs.empty) extends Prog:
  def mod = progs.mod -- locals
  def free = (progs.free ++ attrs.free) -- locals
  def funs = progs.funs ++ attrs.funs
  def returns = progs.exists(_.returns)
  def abstracts = progs.exists(_.abstracts)
  def calls = progs.flatMap(_.calls).toSet

case class Choice(progs: List[Prog]) extends Prog:
  def mod = progs.mod
  def free = progs.free
  def funs = progs.funs
  def returns = progs.exists(_.returns)
  def abstracts = progs.exists(_.abstracts)
  def calls = progs.flatMap(_.calls).toSet

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
  def funs = test.funs ++ left.funs ++ right.funs
  def returns = left.returns || right.returns
  def abstracts = left.abstracts || right.abstracts
  def calls = left.calls ++ right.calls

case class While(test: Expr, body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod
  def free = test.free ++ body.free ++ attrs.free
  def funs = test.funs ++ body.funs ++ attrs.funs
  def returns = body.returns
  def abstracts = attrs.invariants.isEmpty || body.abstracts
  def calls = body.calls

case class Iter(body: Prog, attrs: Attrs) extends Prog:
  def mod = body.mod
  def free = body.free ++ attrs.free
  def funs = body.funs ++ attrs.funs
  def returns = body.returns
  def abstracts = attrs.invariants.isEmpty || body.abstracts
  def calls = body.calls

// a system of ordinary differential equations x' = e for x in xs and e in rhs,
// which evolves for some time within the domain `dom`, the evolution constraint,
// as the continuous evolution of hybrid programs in dL, {x' = e, y' = f & dom},
// the attributes are e.g. differential invariants, as the invariants of loops;
// the time is bound by the evolution, which starts at 0 and has derivative 1, time and xs must be on Real
case class Ode(time: Var, xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs) extends Prog:
  def mod = Set(xs*)
  def free = rhs.free ++ dom.free ++ attrs.free - time ++ xs
  def funs = rhs.funs ++ dom.funs ++ attrs.funs
  def returns = false
  def abstracts = false
  def calls = Set()

// parallel composition of programs, of which verification supports calls to procedures only (see VCGen),
// whose assumption-commitment contracts over the global history of events are in their attributes,
// "assumes" and "commits"; the programs must not share the variables that they modify, other than the history
case class Par(progs: List[Prog]) extends Prog:
  def mod = progs.mod
  def free = progs.free
  def funs = progs.funs
  def returns = progs.exists(_.returns)
  def abstracts = progs.exists(_.abstracts)
  def calls = progs.flatMap(_.calls).toSet

object Par:
  // the variables modified by one program and used by another, other than the global history of events, if it is
  // declared (see State.history)
  def shared(state: State, progs: List[Prog]): Set[Var] =
    val history = state.vars.get("history").toSet
    val pairs =
      for
        (left, i) <- progs.zipWithIndex
        (right, j) <- progs.zipWithIndex
        if i != j
      yield (left.mod -- history) intersect (right.free ++ right.mod -- history)

    pairs.flatten.toSet
