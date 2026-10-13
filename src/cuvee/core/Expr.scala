package cuvee.core

import util.Name
import util.Counter

import cuvee.Error

sealed trait Expr:
  def params: Set[Param]
  def free: Set[Var]
  // the functions that are applied or tested for, also in patterns, excluding those bound by Rec
  def funs: Set[Fun]
  def typ: Type

  // apply `f` to the immediate subexpressions point-wise,
  // the bound variables of binders and combinators are kept, i.e., `f` must avoid capture itself
  // the subexpressions are visited from left to right, such that `f` may be used for its side effects only
  def map(f: Expr => Expr): Expr =
    this match
      case _: Var | _: Lit                    => this
      case App(fun, inst, typ, args)          => App(fun, inst, typ, args.map(f))
      case Distinct(exprs)                    => Distinct(exprs.map(f))
      case Is(arg, fun)                       => Is(f(arg), fun)
      case As(arg, typ)                       => As(f(arg), typ)
      case Diff(xs, arg)                      => Diff(xs, f(arg))
      case Old(arg)                           => Old(f(arg))
      case Trace(inits, deps, accs, bound, results) => Trace(inits.map(f), deps.map(f), accs, bound, results.map(f))
      case Component(trace, i)                => Component(f(trace), i)
      case History(trace, i)                  => History(f(trace), i)
      case Maps(deps, bound, upd)             => Maps(deps.map(f), bound, f(upd))
      case Eps(upds)                          => Eps(upds.map(f))
      case Invs(deps, bound, body)            => Invs(deps.map(f), bound, f(body))
      case Bind(quant, bound, body)           => Bind(quant, bound, f(body))
      case Lam(bound, body, typ)              => Lam(bound, f(body), typ)
      case Let(bound, args, body)             => Let(bound, args.map(f), f(body))
      case Match(arg, cases)                  => Match(f(arg), cases.map(f))
      case Rec(fun, cases)                    => Rec(fun, cases.map(f))

  // the expression without type annotations e as T
  def removeAs: Expr =
    this match
      case As(arg, _) => arg.removeAs
      case _          => map(_.removeAs)

  def isSum =
    this match
      case App(fun, _, Sort.int, _) =>
        fun == Fun.int.uminus || fun == Fun.int.plus || fun == Fun.int.minus

      case App(fun, _, Sort.real, _) =>
        fun == Fun.real.uminus || fun == Fun.real.plus || fun == Fun.real.minus

      case _ =>
        false

  def isArith =
    this match
      case App(fun, _, Sort.int, _) =>
        fun == Fun.int.uminus || fun == Fun.int.plus || fun == Fun.int.minus || fun == Fun.int.times

      case App(fun, _, Sort.real, _) =>
        fun == Fun.real.uminus || fun == Fun.real.plus || fun == Fun.real.minus || fun == Fun.real.times

      case _ =>
        false

  // the type of a comparison is Bool, the functions determine Int or Real
  def isComparison =
    this match
      case App(fun, _, _, _) =>
        fun == Fun.int.le || fun == Fun.int.lt || fun == Fun.real.le || fun == Fun.real.lt

      case _ =>
        false

object Expr:
  // TODO: structural ordering, for now by the printed representation
  given Ordering[Expr] = Ordering.by(_.toString)

  def vars(name: String, types: List[Type]) =
    for (typ, index) <- types.zipWithIndex
    yield Var(Name(name, Some(index)), typ)

case class Var(name: Name, typ: Type) extends Expr:
  def params = typ.params
  def free = Set(this)
  def funs = Set()

  def asPair = (name, typ)
  def asIndex = (name, this)

  def fresh =
    Var(name.withIndex(Var.next()), typ)

  // the variable for the derivative of this one, x'
  def primed =
    Var(name.primed, typ)

object Var extends Counter

case class Lit(value: Any, typ: Type) extends Expr:
  def params = typ.params
  def free = Set()
  def funs = Set()

object App:
  // instantiate the type parameters of `fun` by matching its argument types against those of `args`,
  // where the defined sorts of `state` are unfolded, and expanded in the result (see Type.expand)
  def apply(state: State, fun: Fun, args: List[Expr]): App =
    val inst = args.types
    val su = Type.bind(state, fun.args, inst)
    val typ = Type.expand(state, su(fun.res))
    App(fun, inst, typ, args)

  // the same without defined sorts, where there is no state (e.g. sugar)
  def apply(fun: Fun, args: List[Expr]): App =
    App(State.empty, fun, args)

// the compound expressions cache their hash (lazy, the generated one of case classes), since the memos and classes of
// the engines hash large terms, e.g. the traces of -teq substituted throughout a goal, at every lookup
case class App(fun: Fun, inst: List[Type], typ: Type, args: List[Expr]) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = inst.params ++ args.params
  def free = args.free
  def funs = args.funs + fun

// pairwise distinctness of two or more expressions of the same type, n-ary as in SMT-LIB
case class Distinct(exprs: List[Expr]) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = exprs.params
  def free = exprs.free
  def funs = exprs.funs
  def typ = Sort.bool

// whether `expr` is built by the constructor `fun` of a datatype
case class Is(expr: Expr, fun: Fun) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = expr.params
  def free = expr.free
  def funs = expr.funs + fun
  def typ = Sort.bool

// explicit type annotation, e.g. for polymorphic constants
case class As(expr: Expr, typ: Type) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = expr.params ++ typ.params
  def free = expr.free
  def funs = expr.funs

// the (time-)derivative of `expr` with respect to the variables `xs`, i.e., the sum of ∂expr/∂x * x' for x in xs,
// where the variables xs are ordinary free variables without primes, which are introduced only by computing
// the derivative (see Simplify.diff); xs must be on Real;
// the primed variables are free, too, since the derivative refers to them once it is computed
case class Diff(xs: List[Var], expr: Expr) extends Expr:
  def params = xs.params ++ expr.params
  def free = expr.free ++ xs ++ xs.primed
  def funs = expr.funs
  def typ = expr.typ

// the value of `expr` at the entry of the enclosing procedure, where the global variables have their initial values,
// eliminated by `Old.elim` before verification
case class Old(expr: Expr) extends Expr:
  def params = expr.params
  def free = expr.free
  def funs = expr.funs
  def typ = expr.typ

object Old:
  // replace old(e) by e[gs := gs_], where gs_ are the values of the global variables gs at the entry,
  // nested occurrences of old refer to the same values
  def elim(gs: List[Var], gs_ : List[Expr], expr: Expr): Expr =
    instance(Subst.empty, Subst.from(gs, gs_), expr)

  // a single traversal that replaces the free variables by `now`, and inside of old(e) by `before`, and strips old,
  // e.g. for the postcondition of a call, whose modified global variables refer to their new values outside of old
  // and to their values before the call inside of it (see VCGen.instance); `Subst` substitutes inside old(e) as well;
  // the type parameters are instantiated by `now`
  def instance(now: Subst[Type, Expr], before: Subst[Type, Expr], expr: Expr): Expr =
    instance(now, before, false, expr)

  // `old` holds inside of old(e)
  def instance(now: Subst[Type, Expr], before: Subst[Type, Expr], old: Boolean, expr: Expr): Expr =
    val su = if old then before else now

    // the variables bound in the context are no longer replaced, those that would capture
    // a free variable of the replacements are renamed, also in the patterns of cases
    def bind(xs: List[Var]): (List[Var], Expr => Expr) =
      val (rename, now_) = now.avoid(xs, now.free ++ before.free)
      val before_ = Subst(before.params, before.vars -- xs ++ rename.vars)
      (rename.lhs(xs), instance(now_, before_, old, _))

    expr match
      case x: Var                    => su(x)
      case Lit(value, typ)           => Lit(value, now(typ))
      case App(fun, inst, typ, args) => App(fun, now(inst), now(typ), args.map(instance(now, before, old, _)))
      case As(arg, typ)              => As(instance(now, before, old, arg), now(typ))
      case Diff(xs, arg)             => Diff(su.lhs(xs), instance(now, before, old, arg))
      case Old(arg)                  => instance(now, before, true, arg)

      case Bind(quant, bound, body) =>
        val (bound_, inner) = bind(bound)
        Bind(quant, bound_, inner(body))

      case Lam(bound, body, typ) =>
        val (bound_, inner) = bind(bound)
        Lam(bound_, inner(body), now(typ))

      case Trace(inits, deps, accs, bound, results) =>
        val (vars_, inner) = bind(accs ++ bound)
        val (accs_, bound_) = vars_.splitAt(accs.length)
        Trace(inits.map(instance(now, before, old, _)), deps.map(instance(now, before, old, _)), accs_, bound_, results.map(inner))

      case Component(trace, i) => Component(instance(now, before, old, trace), i)
      case History(trace, i)   => History(instance(now, before, old, trace), i)

      case Maps(deps, bound, update) =>
        val (bound_, inner) = bind(bound)
        Maps(deps.map(instance(now, before, old, _)), bound_, inner(update))

      case Invs(deps, bound, body) =>
        val (bound_, inner) = bind(bound)
        Invs(deps.map(instance(now, before, old, _)), bound_, inner(body))

      case Let(bound, args, body) =>
        val (bound_, inner) = bind(bound)
        Let(bound_, args.map(instance(now, before, old, _)), inner(body))

      case Match(arg, cases) =>
        val cases_ =
          for Case(pat, body, cond) <- cases
          yield
            val (_, inner) = bind(pat.free.toList)
            Case(inner(pat), inner(body), inner(cond))
        Match(instance(now, before, old, arg), cases_)

      // the type parameters of the function are bound, hence not instantiated
      case Rec(fun, _) if fun.params.exists(p => now.params.contains(p) || before.params.contains(p)) =>
        val now_ = Subst(now.params -- fun.params, now.vars)
        val before_ = Subst(before.params -- fun.params, before.vars)
        instance(now_, before_, old, expr)

      case Rec(fun, cases) =>
        val cases_ =
          for Case(pat, body, cond) <- cases
          yield
            val (_, inner) = bind(pat.free.toList)
            Case(inner(pat), inner(body), inner(cond))
        Rec.retype(fun, now(_: Type), cases_)

      case _ =>
        expr.map(instance(now, before, old, _))

  // in all expressions and attributes of a program, e.g. assertions and loop invariants
  def elim(gs: List[Var], gs_ : List[Expr], prog: Prog): Prog =
    prog.map(elim(gs, gs_, _: Expr), elim(gs, gs_, _: Prog))

// the combinators of trace equation systems, which describe the computation of a loop per variable;
// their dependencies `deps` are sequences of the same length, over which the variables `bound` range point-wise,
// and their updates are expressions, a single result or guarded results Eps(...) with disjoint guards,
// which need not be complete, e.g. the paths that continue a loop with break
//
// a case of Eps, if φ then e, as Upd(φ, e)
case class Upd(cond: Expr, rhs: Expr):
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = cond.params ++ rhs.params
  def free = cond.free ++ rhs.free
  def funs = cond.funs ++ rhs.funs

  def map(f: Expr => Expr) =
    Upd(f(cond), f(rhs))

// a variant of Hilbert's choice over guarded results, if φ₁ then e₁, ..., if φₚ then eₚ:
// some eᵢ whose guard φᵢ holds, a value that is not specified if none holds
case class Eps(updates: List[Upd]) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = updates.params
  def free = updates.free
  def funs = updates.funs

  // there is at least one case, see Type.check
  def typ = updates.head.rhs.typ

object Eps:
  // the cases of nested choices as one list, whose guards are the conjunctions of the guards along the way,
  // e.g. if p then (if q then x, if !q then y), if !p then y is if p && q then x, if p && !q then y, if !p then y
  def flatten(updates: List[Upd]): List[Upd] =
    for
      Upd(cond, rhs) <- updates
      upd <-
        rhs match
          case Eps(inner) => flatten(inner).map(upd => Upd(And(List(cond, upd.cond).conjuncts), upd.rhs))
          case _          => List(Upd(cond, rhs))
    yield upd

// trace(inits, for deps do accs, bound ↦ results): the trace of the values of the accumulators `accs`, starting
// from `inits`, where each subsequent value is computed by the results from the previous ones and the corresponding
// values of the dependencies, one entry longer than the dependencies; one accumulator for a variable of a loop that
// depends on no other, several for the variables of a cycle (see ideas/deduction-engine-plan.md, section 1.4), whose
// values are tuples in the type only (Trace<(T₁, ..., Tₘ)>): no term of tuple type is built, the components are read
// by Component and History
case class Trace(inits: List[Expr], deps: List[Expr], accs: List[Var], bound: List[Var], results: List[Expr]) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = inits.params ++ deps.params ++ (accs ++ bound).params ++ results.params
  def free = inits.free ++ deps.free ++ (results.free -- (accs ++ bound))
  def funs = inits.funs ++ deps.funs ++ results.funs
  def typ = Sort.trace(Trace.elem(accs.types))

object Trace:
  // a trace of a single accumulator, as in the paper, the common case
  def apply(init: Expr, deps: List[Expr], acc: Var, bound: List[Var], update: Expr): Trace =
    Trace(List(init), deps, List(acc), bound, List(update))

  // the element type of a trace with the given component types: the type itself for one, a tuple type for several
  def elem(types: List[Type]): Type =
    types match
      case List(typ) => typ
      case _         => Sort(Con(Tuples.name(types.length), types.length), types)

  // the component types of the element type of a trace (see elem)
  def components(elem: Type): List[Type] =
    elem match
      case Sort(Con(name, arity), args) if name == Tuples.name(arity) && arity >= 2 => args
      case _                                                                     => List(elem)

  // the traces of a single accumulator, which the lemma database and the lowering handle; a trace of several
  // accumulators does not match
  object single:
    def unapply(trace: Trace): Option[(Expr, List[Expr], Var, List[Var], Expr)] =
      trace match
        case Trace(List(init), deps, List(acc), bound, List(update)) => Some((init, deps, acc, bound, update))
        case _                                                       => None

// current(S).i, the component i of the last value of a trace of several accumulators, and ⌊S⌋.i, the history of that
// component, a list of the ordinary type List<Tᵢ>: the only ways to read a component, such that the tuple type of the
// trace never appears in a term; typed by the component types of the trace (see Trace.components)
case class Component(trace: Expr, index: Int) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = trace.params
  def free = trace.free
  def funs = trace.funs
  def typ = Component.typ(trace.typ, index)

object Component:
  def typ(trace: Type, index: Int): Type =
    trace match
      case Sort(Con.trace, List(elem)) => Trace.components(elem)(index)
      case _                           => Error.raise("component of an expression that is not a trace", trace, index)

case class History(trace: Expr, index: Int) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = trace.params
  def free = trace.free
  def funs = trace.funs
  def typ = Sort.list(Component.typ(trace.typ, index))

// map(for deps yield bound ↦ update): the list of the results of the update for the values of the dependencies,
// point-wise, which has the same length as the dependencies
case class Maps(deps: List[Expr], bound: List[Var], update: Expr) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = deps.params ++ bound.params ++ update.params
  def free = deps.free ++ (update.free -- bound)
  def funs = deps.funs ++ update.funs
  def typ = Sort.list(update.typ)

// all(for deps check bound ↦ body): the condition holds for all values of the dependencies, point-wise
case class Invs(deps: List[Expr], bound: List[Var], body: Expr) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = deps.params ++ bound.params ++ body.params
  def free = deps.free ++ (body.free -- bound)
  def funs = deps.funs ++ body.funs
  def typ = Sort.bool

case class Bind(quant: Name, bound: List[Var], body: Expr) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = bound.params ++ body.params
  def free = body.free -- bound
  def funs = body.funs
  def typ = body.typ

// an anonymous function, whose type is explicit, since it is not determined by the bound variables and the body:
// for now an array, as the lambda of SMT-LIB, of a single bound variable (see Type.check)
case class Lam(bound: List[Var], body: Expr, typ: Type) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = bound.params ++ body.params ++ typ.params
  def free = body.free -- bound
  def funs = body.funs

case class Let(bound: List[Var], args: List[Expr], body: Expr) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = bound.params ++ args.params ++ body.params
  def free = args.free ++ (body.free -- bound)
  def funs = args.funs ++ body.funs
  def typ = body.typ

// a case of a match expression, which applies if the argument matches the pattern and the condition holds,
// the pattern consists of variables and constructor applications (see Type.check), whose variables are bound
// in the body and the condition; conditions are not part of SMT-LIB, where they are always true
case class Case(pat: Expr, body: Expr, cond: Expr):
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def bound = pat.free
  def params = pat.params ++ body.params ++ cond.params
  def free = body.free ++ cond.free -- bound
  def funs = pat.funs ++ body.funs ++ cond.funs

  // the pattern is kept, like the bound variables of binders
  def map(f: Expr => Expr) =
    Case(pat, f(body), f(cond))

// the result of the first case whose pattern matches `arg` and whose condition holds
case class Match(arg: Expr, cases: List[Case]) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = arg.params ++ cases.params
  def free = arg.free ++ cases.free
  def funs = arg.funs ++ cases.funs

  // there is at least one case, see Type.check
  def typ = cases.head.body.typ

// a recursive function, like a lambda that may call itself: `fun` is bound in the cases, whose patterns are
// applications fun(p₁, ..., pₙ) to patterns of the arguments, and whose conditions are guards; applied to arguments,
// the result is that of the first case whose pattern matches and whose condition holds, recursive calls are
// applications of `fun`; the type parameters of `fun` are bound as well, rigid in the cases and instantiated
// freshly at each use, like those of a declared function, and its types may refer to those of the context
case class Rec(fun: Fun, cases: List[Case]) extends Expr:
  override lazy val hashCode: Int = scala.runtime.ScalaRunTime._hashCode(this)
  def params = (fun.args.params ++ fun.res.params ++ cases.params) -- fun.params
  def free = cases.free
  // the recursive calls by name, since their types may be instantiated
  def funs = cases.funs.filterNot(_.name == fun.name)

  // generic in the type parameters of `fun`, see Type.check
  def typ = Arrow(fun.args, fun.res)

object Rec:
  // the function with its types mapped by `su`, also its type parameters, which must be mapped to type parameters,
  // and the recursive calls in the cases, whose types are mapped already, to the new function, since a function
  // is identified by its types (see Fun.equals)
  def retype(fun: Fun, su: Type => Type, cases: List[Case]): Rec =
    val params_ =
      for p <- fun.params
      yield su(p) match
        case p_ : Param => p_
        case typ        => Error.raise("type parameter of a recursive function mapped to a type", fun, p, typ)

    val fun_ = Fun(fun.name, params_, fun.formals.map(x => Var(x.name, su(x.typ))), su(fun.res))

    if fun_ == fun
    then Rec(fun, cases)
    else
      val cases_ =
        for Case(pat, body, cond) <- cases
        yield Case(calls(fun, fun_, pat), calls(fun, fun_, body), calls(fun, fun_, cond))
      Rec(fun_, cases_)

  // the definition fun(x₁, ..., xₙ) = body as a recursive function: a match on one of the formal parameters, xᵢ,
  // gives one case per case of the match, with its pattern in place of xᵢ, its condition as the guard, and the pattern
  // in place of xᵢ in its body and guard, unless the pattern binds xᵢ itself; the other parameters are renamed apart
  // from the variables of the pattern, which shadow them; other bodies give a single case fun(x₁, ..., xₙ) => body
  def from(state: State, fun: Fun, body: Expr): Rec =
    // the body refers to the formal parameters with the defined sorts expanded (see Type.expand)
    val formals = Type.expand(state, fun.formals)

    body match
      case Match(x: Var, cases) if formals.contains(x) =>
        val index = formals.indexOf(x)
        val cases_ =
          for Case(pat, rhs, cond) <- cases
          yield
            val (formals_, _) = Subst.rename(formals, pat.free)
            val args = formals_.patch(index, List(pat), 1)
            val inst = if pat.free.contains(x) then Subst.empty else Subst.from(List(x), List(pat))
            Case(App(fun, args.types, fun.res, args), inst(rhs), inst(cond))
        Rec(fun, cases_)

      case _ =>
        Rec(fun, List(Case(App(fun, formals.types, fun.res, formals), body, True)))

  // the definition of `fun` in `state` as a recursive function
  def from(state: State, fun: Fun): Rec =
    val key = (fun.name, fun.arity)
    Error.report("function not defined", fun):
      require(state.fundefs.contains(key))
    from(state, fun, state.fundefs(key))

  // the applications of `fun` replaced by those of `fun_`
  def calls(fun: Fun, fun_ : Fun, expr: Expr): Expr =
    expr match
      case App(`fun`, inst, typ, args) => App(fun_, inst, typ, args.map(calls(fun, fun_, _)))
      case _                           => expr.map(calls(fun, fun_, _))
