package cuvee.chc

import util.Name
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.sexpr.Attrs

object Verify extends Transform:
  def apply(prefix: List[Cmd], cmds: List[Cmd], last: Cmd, state: State): List[Cmd] =
    for
      cmd <- cmds;
      cmd_ <- verify(state, cmd)
    yield cmd_

  def verify(state: State, cmd: Cmd): List[Cmd] =
    cmd match
      // procedures without body have nothing to verify,
      // their contract is looked up from the state at call sites
      case DeclareProc(proc, attrs) =>
        Nil

      case DefineProc(Proc(name, params, _, _), body, _) =>
        val (in, out, pre, post) = contract(state, name)
        val phi_ = All(in ++ out, Imp(pre, wp(state, name, body, post, False, False, post)))
        List(Assert(Goal, params, phi_, Attrs.empty))

      case _ =>
        List(cmd)

  // formal parameters, precondition, and postcondition of procedure `name`
  def contract(state: State, name: Name): (List[Var], List[Var], Expr, Expr) =
    Error.report("procedure not declared", name):
      require(state.procs.contains(name))

    val Proc(_, _, in, out) = state.procs(name)
    val attrs = state.procattrs(name)
    val pre = And(attrs.values[Expr]("requires"))
    val post = And(attrs.values[Expr]("ensures"))
    (in, out, pre, post)

  // the termination measure of procedure `name`, the components of a lexicographic order,
  // which is evaluated at the entry of the procedure, therefore it must refer to the inputs only,
  // which are never modified
  def measure(state: State, name: Name): List[Expr] =
    val Proc(_, _, in, _) = state.procs(name)
    val dec = state.procattrs(name).values[Expr]("decreases")

    Error.report("termination measure refers to variables other than the inputs", name, dec):
      require(dec.free subsetOf in.toSet)

    dec

  // `next` is smaller than `prev` in the lexicographic order over the integers bounded from below by 0,
  // as in Dafny, i.e., some component decreases and is nonnegative before, and all components before it are equal;
  // without a measure, termination is not checked
  def decreases(next: List[Expr], prev: List[Expr]): Expr =
    Error.report("termination measures of different lengths", next, prev):
      require(next.length == prev.length)

    if prev.isEmpty
    then True
    else
      val cases =
        for i <- prev.indices.toList
        yield And(Eq(next.take(i), prev.take(i)) ++ List(Le(Zero, prev(i)), Lt(next(i), prev(i))))
      Or(cases)

  // weakest preconditions need a separate postcondition for each way a program can terminate:
  // normally, by break, by continue, and by return;
  // `proc` is the procedure that contains the program, whose recursive calls must decrease its measure
  def wp(state: State, proc: Name, progs: List[Prog], post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
    progs.foldRight(post):
      case (prog, phi) =>
        wp(state, proc, prog, phi, break, continue, return_)

  def wp(state: State, proc: Name, prog: Prog, post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
    prog match
      case Break =>
        break

      case Continue =>
        continue

      case Return =>
        return_

      case Spec(xs, pre, phi) =>
        And(pre, All(xs, Imp(phi, post)))

      case Assign(xs, rhs) =>
        val su = Subst.from(xs, rhs)
        su(post)

      case Call(name, args, res) =>
        val (in, out, pre, phi) = contract(state, name)

        Error.report("wrong number of arguments or results in call", name, args, res):
          require(in.length == args.length && out.length == res.length)

        // results are fresh since `args` may refer to the old values of `res`
        val res_ = res.fresh
        val su = Subst.from(in ++ out, args ++ res_)
        val rename = Subst.from(res, res_)

        // the measure refers to the inputs, whose values at the call are those at the entry of `proc`
        val dec =
          if name == proc
          then
            val dec = measure(state, proc)
            decreases(su(dec), dec)
          else True

        And(List(su(pre), dec, All(res_, Imp(su(phi), rename(post)))))

      case Block(locals, progs) =>
        // locals may shadow variables in the postcondition, therefore they are renamed apart
        val locals_ = locals.fresh
        val su = Subst.from(locals, locals_)
        All(locals_, wp(state, proc, su(progs), post, break, continue, return_))

      case Choice(progs) =>
        And(progs.map(wp(state, proc, _, post, break, continue, return_)))

      case If(test, left, right) =>
        val left_ = Imp(test, wp(state, proc, left, post, break, continue, return_))
        val right_ = Imp(Not(test), wp(state, proc, right, post, break, continue, return_))
        And(left_, right_)

      case While(test, body, attrs) =>
        val inv = And(attrs.values[Expr]("invariant"))
        val xs = body.mod.toList

        // the measure must decrease from the start to the end of each iteration, i.e., also on continue,
        // its values at the start are the fresh variables ms, which are replaced by the measure afterwards
        val dec = attrs.values[Expr]("decreases")
        val ms = Expr.vars("m", dec.map(_.typ)).fresh
        val su = Subst.from(ms, dec)
        val iter = And(inv, decreases(dec, ms))

        val step = Imp(test, su(wp(state, proc, body, iter, post, iter, return_)))
        val exit = Imp(Not(test), post)

        And(inv, All(xs, Imp(inv, And(step, exit))))
