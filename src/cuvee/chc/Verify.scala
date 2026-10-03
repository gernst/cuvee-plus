package cuvee.chc

import util.Name
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.sexpr.Attrs

object Verify extends Transform:
  def apply(prefix: List[Cmd], cmds: List[Cmd], state: State): List[Cmd] =
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
        val phi_ = All(in ++ out, Imp(pre, wp(state, body, post, False, False, post)))
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

  // weakest preconditions need a separate postcondition for each way a program can terminate:
  // normally, by break, by continue, and by return
  def wp(state: State, progs: List[Prog], post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
    progs.foldRight(post):
      case (prog, phi) =>
        wp(state, prog, phi, break, continue, return_)

  def wp(state: State, prog: Prog, post: Expr, break: Expr, continue: Expr, return_ : Expr): Expr =
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
        And(su(pre), All(res_, Imp(su(phi), rename(post))))

      case Block(locals, progs) =>
        // locals may shadow variables in the postcondition, therefore they are renamed apart
        val locals_ = locals.fresh
        val su = Subst.from(locals, locals_)
        All(locals_, wp(state, su(progs), post, break, continue, return_))

      case Choice(progs) =>
        And(progs.map(wp(state, _, post, break, continue, return_)))

      case If(test, left, right) =>
        val left_ = Imp(test, wp(state, left, post, break, continue, return_))
        val right_ = Imp(Not(test), wp(state, right, post, break, continue, return_))
        And(left_, right_)

      case While(test, body, attrs) =>
        val inv = And(attrs.values[Expr]("invariant"))
        val xs = body.mod.toList

        val step = Imp(test, wp(state, body, inv, post, inv, return_))
        val exit = Imp(Not(test), post)

        And(inv, All(xs, Imp(inv, And(step, exit))))
