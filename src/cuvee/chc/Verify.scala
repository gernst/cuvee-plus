package cuvee.chc

import util.Name
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import cuvee.sexpr.Attrs

// verification conditions are computed by weakest preconditions,
// which need a separate postcondition for each way a program can terminate
case class Post(normal: Expr, break: Expr, continue: Expr, ret: Expr)

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
        val post_ = Post(post, False, False, post)
        val phi_ = all(in ++ out, Imp(pre, wp(state, body, post_)))
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

  def wp(state: State, progs: List[Prog], post: Post): Expr =
    progs.foldRight(post.normal):
      case (prog, phi) =>
        wp(state, prog, post.copy(normal = phi))

  def wp(state: State, prog: Prog, post: Post): Expr =
    prog match
      case Break =>
        post.break

      case Continue =>
        post.continue

      case Return =>
        post.ret

      case Spec(xs, pre, phi) =>
        And(pre, all(xs, Imp(phi, post.normal)))

      case Assign(xs, rhs) =>
        val su = Subst.from(xs, rhs)
        su(post.normal)

      case Call(name, args, res) =>
        val (in, out, pre, phi) = contract(state, name)

        Error.report("wrong number of arguments or results in call", name, args, res):
          require(in.length == args.length && out.length == res.length)

        // results are fresh since `args` may refer to the old values of `res`
        val res_ = res.fresh
        val su = Subst.from(in ++ out, args ++ res_)
        val rename = Subst.from(res, res_)
        And(su(pre), all(res_, Imp(su(phi), rename(post.normal))))

      case Block(locals, progs) =>
        // locals may shadow variables in the postcondition, therefore they are renamed apart
        val locals_ = locals.fresh
        val su = Subst.from(locals, locals_)
        all(locals_, wp(state, su(progs), post))

      case Choice(progs) =>
        And(progs.map(wp(state, _, post)))

      case If(test, left, right) =>
        val left_ = Imp(test, wp(state, left, post))
        val right_ = Imp(Not(test), wp(state, right, post))
        And(left_, right_)

      case While(test, body, attrs) =>
        val inv = And(attrs.values[Expr]("invariant"))
        val xs = body.mod.toList

        val post_ = Post(inv, post.normal, inv, post.ret)
        val step = Imp(test, wp(state, body, post_))
        val exit = Imp(Not(test), post.normal)

        And(inv, all(xs, Imp(inv, And(step, exit))))

  // SMT-LIB does not admit quantifiers without bound variables
  def all(xs: List[Var], phi: Expr): Expr =
    if xs.isEmpty
    then phi
    else All(xs, phi)
