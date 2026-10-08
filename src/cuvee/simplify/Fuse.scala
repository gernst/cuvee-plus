package cuvee.simplify

import cuvee.Config
import cuvee.Error
import cuvee.pipe.Transform
import cuvee.core._
import util.Name
import util.intersects

// fixpoint fusion (deforestation): the composition g(f(x₁, ..., xₙ), y₁, ..., yₘ) of two recursive functions,
// where g consumes the result of f in its first argument, as a single recursive function h(x₁, ..., xₙ, y₁, ..., yₘ)
// with one case per case of f, f(p₁, ..., pₙ) if φ => e, namely h(p₁, ..., pₙ, y₁, ..., yₘ) if φ => g(e, y₁, ..., yₘ),
// where g is driven into e:
// - a recursive call f(t₁, ..., tₙ) becomes h(t₁, ..., tₙ, y₁, ..., yₘ), which closes the fixpoint;
// - a conditional is driven into its branches;
// - a constructor application selects the cases of g statically in their order, a case whose pattern does not match
//   is skipped, one whose pattern matches is instantiated, with its guard as a test before the remaining cases,
//   and in its body, g(f(t₁, ..., tₙ), z₁, ..., zₘ) becomes h(t₁, ..., tₙ, z₁, ..., zₘ);
// - otherwise, and once a pattern is undecided, i.e., it has a constructor where the expression has none,
//   or a case of g has a pattern for one of its other arguments, the result is g applied as a function value;
// the remaining recursive calls of f and g outside of these positions are applications of f and g as function values;
// the result is equivalent to the composition, if f and g are total and their recursion is monomorphic
//
// as a stage (-fuse), the requests fuse g(f(xs), ys) = ??? get the fusion of the definitions of g and f as their
// right-hand side, whose formal parameters are the variables xs and ys of the request
object Fuse extends Transform:
  // whether a pattern matches an expression, by an instantiation of its variables
  enum Outcome:
    case Matches(su: Map[Var, Expr])
    case Fails
    case Undecided

  def apply(config: Config, state: State, prefix: List[Cmd], cmds: List[Cmd], last: Cmd): List[Cmd] =
    for cmd <- cmds
    yield cmd match
      case FuseFuns(term, None, attrs) => FuseFuns(term, Some(fuse(state, term)), attrs)
      case _                           => cmd

  // the composition g(f(xs), ys) of two defined functions as a recursive function of the distinct variables xs and ys
  def fuse(state: State, term: Expr): Rec =
    term match
      case App(gf, _, _, App(ff, _, _, args) :: rest) =>
        val xs = (args ++ rest).collect { case x: Var => x }
        Error.report("fuse needs distinct variables as the arguments", term):
          require(xs.length == args.length + rest.length && xs.distinct == xs)

        val Rec(hf, cases) = apply(state, Rec.from(state, gf), Rec.from(state, ff))
        val ys = xs.drop(args.length)

        // the further parameters of the cases, which are fresh, are named like the variables of the request,
        // unless a variable of the pattern of f has that name already
        val cases_ =
          for case Case(pat @ App(_, _, _, pats), body, cond) <- cases
          yield
            val zs = pats.takeRight(ys.length).collect { case z: Var => z }
            if (pat.free -- zs) intersects ys.toSet
            then Case(pat, body, cond)
            else
              val re = Subst.from(zs, ys)
              Case(re(pat), re(body), re(cond))

        Rec(Fun(hf.name, hf.params, xs, hf.res), cases_)

      case _ =>
        Error.raise("fuse needs a composition g(f(x₁, ..., xₙ), y₁, ..., yₘ) of two defined functions", term)

  def apply(state: State, g: Rec, f: Rec): Rec =
    val Rec(gf, gcases) = g
    val Rec(ff, fcases) = f

    Error.report("cannot fuse, the result of the inner function is not the first argument of the outer one", ff, gf):
      require(gf.args.nonEmpty && gf.args.head == ff.res)

    val ys = gf.formals.tail.map(_.fresh)
    val hf = Fun(Name(gf.name.name + "_" + ff.name.name, None), (ff.params ++ gf.params).distinct, ff.formals ++ ys, gf.res)

    val hcases =
      for Case(pat, body, cond) <- fcases
      yield pat match
        case App(`ff`, _, _, ps) =>
          Case(call(hf, ps ++ ys), drive(state, g, f, hf, ys, body), values(g, f, hf, cond))

        case _ =>
          Error.raise("pattern does not apply the recursive function", pat, ff)

    Rec(hf, hcases)

  // an application of `fun` with the types of the arguments, monomorphic in its type parameters
  def call(fun: Fun, args: List[Expr]): App =
    App(fun, args.types, fun.res, args)

  // g(e, ys) with g driven into e
  def drive(state: State, g: Rec, f: Rec, hf: Fun, ys: List[Var], e: Expr): Expr =
    e match
      case App(fun, _, _, args) if fun == f.fun =>
        call(hf, args.map(values(g, f, hf, _)) ++ ys)

      case Ite(test, left, right) =>
        Ite(values(g, f, hf, test), drive(state, g, f, hf, ys, left), drive(state, g, f, hf, ys, right))

      case _ =>
        select(state, g, f, hf, ys, e, g.cases)

  // the first of the cases of g that applies to (e, ys), whose guards are tested in order
  def select(state: State, g: Rec, f: Rec, hf: Fun, ys: List[Var], e: Expr, cases: List[Case]): Expr =
    def fallback =
      Apply(g, values(g, f, hf, e) :: ys)

    cases match
      case Nil =>
        fallback

      case Case(pat, body, cond) :: rest =>
        val (_, re) = Subst.rename(pat.free.toList)
        val App(_, _, _, q :: qs) = re(pat): @unchecked
        val zs = qs.collect { case z: Var => z }

        if zs.length < qs.length then fallback
        else
          matches(state, q, e) match
            case Outcome.Fails =>
              select(state, g, f, hf, ys, e, rest)

            case Outcome.Undecided =>
              fallback

            case Outcome.Matches(su) =>
              val inst = Subst(Map(), su ++ (zs zip ys))
              val body_ = values(g, f, hf, inst(re(body)))
              val cond_ = values(g, f, hf, inst(re(cond)))

              if cond_ == True
              then body_
              else Ite(cond_, body_, select(state, g, f, hf, ys, e, rest))

  // the pattern against the expression, whose constructor applications decide the constructors of the pattern
  def matches(state: State, pat: Expr, expr: Expr): Outcome =
    (pat, expr) match
      case (x: Var, _) =>
        Outcome.Matches(Map(x -> expr))

      case (App(con, _, _, pats), App(con_, _, _, args)) if state.constrs.get(con_.name) == Some(con_) =>
        if con != con_
        then Outcome.Fails
        else matches(state, pats, args)

      case _ =>
        Outcome.Undecided

  // the patterns against the arguments, which fail if one fails, and are undecided if one is undecided otherwise
  def matches(state: State, pats: List[Expr], args: List[Expr]): Outcome =
    val outcomes = (pats zip args).map(matches(state, _, _))
    val sus = outcomes.collect { case Outcome.Matches(su) => su }

    if outcomes.contains(Outcome.Fails) then Outcome.Fails
    else if outcomes.contains(Outcome.Undecided) then Outcome.Undecided
    else Outcome.Matches(sus.flatten.toMap)

  // the recursive calls of g and f in `expr`: g(f(t₁, ..., tₙ), z₁, ..., zₘ) as h(t₁, ..., tₙ, z₁, ..., zₘ), the others as
  // applications of the function values g and f
  def values(g: Rec, f: Rec, hf: Fun, expr: Expr): Expr =
    expr match
      case App(fun, _, _, App(fun_, _, _, args) :: rest) if fun == g.fun && fun_ == f.fun =>
        call(hf, (args ++ rest).map(values(g, f, hf, _)))

      case App(fun, _, _, args) if fun == g.fun =>
        Apply(g, args.map(values(g, f, hf, _)))

      case App(fun, _, _, args) if fun == f.fun =>
        Apply(f, args.map(values(g, f, hf, _)))

      case _ =>
        expr.map(values(g, f, hf, _))
