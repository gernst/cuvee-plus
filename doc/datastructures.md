# Data structures

The core representation in [`cuvee.core`](../src/cuvee/core). All frontends
produce it, and all transforms and printers consume it. Every class is an
immutable case class, and the sealed traits make pattern matches checked for
exhaustiveness.

## Names

`util.Name(name: String, index: Option[Int])`

- An index distinguishes fresh copies, e.g. `x$3`. It is printed as `x$3` in
  SMT-LIB and as `x₃` in Dafny.
- A string converts implicitly to a `Name`, and `"x$3"` becomes
  `Name("x", Some(3))`.
- `Name.primed` appends `'`; derivatives use it ([hybrid.md](hybrid.md)).

## Types ([Type.scala](../src/cuvee/core/Type.scala))

```scala
case class Con(name: Name, arity: Int)          // sort constructor, e.g. Array/2
sealed trait Type
case class Param(name: Name) extends Type       // type parameter
case class Sort(con: Con, args: List[Type]) extends Type
case class BitVec(n: Int) extends Type          // (_ BitVec n)
```

- Built-in sorts:
  - `Sort.bool`, `Sort.int`, `Sort.real`, `Sort.string`;
  - `Sort.array(dom, ran)`, `Sort.seq(elem)`, `Sort.set(elem)`,
    `Sort.bag(elem)`, `Sort.trace(elem)` ([teq.md](teq.md)).
- Bitvectors `BitVec(n)` are a type of their own, since their functions are
  polymorphic in the width, which type parameters cannot express;
  `BitVecs.fun` instantiates them for the widths of the arguments.
  `Overload` resolves the operators of the frontends on them by the width
  (`Overload.bitvectors`) and the conversions `as_int`/`as_bv` by the
  target type as well (`Overload.conversion`).
- Numeric literals may have an open type (Dafny): `Type.instantiate`
  defaults it to `Int` and reduces literals of bitvectors modulo `2^n`.
- Defined sorts (`define-sort`, Dafny `type T = ...`) are unfolded on
  demand by `Type.unfold` (at the top) during type checking (`unify`,
  `bind`). Afterwards, `State.exprs.check` and `State.progs.check` expand
  them (`Type.expand`) in all types of expressions and programs, including
  variables and bound variables, before overloading is resolved;
  `App(state, fun, args)` expands the result type. Declarations keep them,
  e.g. formal parameters, global variables, and modifies clauses, which
  `VCGen`, `Horn`, `TEQ`, `Rule.from`, and `Flat` expand where they meet
  bodies, since variables are compared with their types. Overloading,
  rewriting, `Ring`, and `Monomorph` see expanded types only.
- `Type.unify` drives type checking. It respects rigid parameters: those of
  the enclosing declaration, kept in the `Scope`.
- `Type.bind` matches a signature against argument types. `App(fun, args)`
  has no state and does not unfold defined sorts.

## Functions ([Fun.scala](../src/cuvee/core/Fun.scala))

```scala
case class Fun(name: Name, params: List[Param], formals: List[Var], res: Type)
```

- Functions are polymorphic in `params` and identified by name and arity.
  Overloading by arity is allowed, e.g. unary and binary `-`.
- The built-in functions are values in `Fun`:
  - `Fun.eq_`, `Fun.ite`, `Fun.select`, `Fun.store`, `Fun.and`, ...;
  - `Fun.int.*` and `Fun.real.*` for arithmetic;
  - `Fun.seq.*` for sequences, named as in cvc5: `seq.++`, `seq.len`,
    `seq.nth`, ...
- Their formal parameters are named `x$0, x$1, ...`, as in the SMT-LIB
  prelude, so that declarations parsed from a prelude are equal to these
  values.

## Expressions ([Expr.scala](../src/cuvee/core/Expr.scala))

```scala
sealed trait Expr { def params: Set[Param]; def free: Set[Var]; def typ: Type }

case class Var(name: Name, typ: Type)
case class Lit(value: Any, typ: Type)          // BigInt, util.Rational, String
case class App(fun: Fun, inst: List[Type], typ: Type, args: List[Expr])
case class Distinct(exprs: List[Expr])
case class Is(expr: Expr, fun: Fun)            // tester of a datatype constructor
case class As(expr: Expr, typ: Type)           // type annotation
case class Diff(xs: List[Var], expr: Expr)     // derivative (xs :: expr)'
case class Old(expr: Expr)                     // value at the entry of the procedure
case class Bind(quant: Name, bound: List[Var], body: Expr)   // forall, exists
case class Lam(bound: List[Var], body: Expr, typ: Type)      // an array of one index, or a function (Arrow)
case class Let(bound: List[Var], args: List[Expr], body: Expr)
case class Match(arg: Expr, cases: List[Case])  // the first case that matches and whose condition holds
case class Case(pat: Expr, body: Expr, cond: Expr)  // pattern variables are bound in body and cond
case class Rec(fun: Fun, cases: List[Case])     // recursive function, cases fun(p₁, ..., pₙ) if cond => body

// the combinators of trace equation systems, see teq.md
case class Trace(...); case class Maps(...); case class Invs(...)
```

- **Function types** `(A₁, ..., Aₙ) -> R` of Dafny are the sorts `arrow₁`,
  ..., `arrow₁₀` of its prelude, whose last argument is the result
  (`Arrow(args, res)` builds and matches them). Their lambdas
  `(x: A, y: B) => e` always annotate the variables and are built by
  `state.exprs.lam`; Boogie does not print them, SMT-LIB prints them as
  `lambda` of function type but does not read them back. Function values
  are applied by `apply₁`, ..., `apply₁₀` of the prelude (`Apply(f, args)`);
  Dafny resolves `f(a)` as the application of a variable of function type,
  then of a function, then of a constant of function type, then of a member.
  Tuples, function types, and applications are indexed names, `tuple₂`
  (`tuple$2` in SMT-LIB). The declarations of the function types and the
  applications are higher-order (`{:ho}`) and not passed to solvers; SMT-LIB
  prints and parses them as in SMT-LIB 2.7, `(-> A B C)` and `(@ f a b)`,
  where `@` is left-associative (see TODO.md).
- **Lambdas and arrays of several indices.** `Lam` has an explicit type, an
  array of a single index or a function of its variables (`Type.check`). Several variables and indices are
  nested (curried): `Lams(xs, e)` builds and collects nested lambdas,
  `Arrays(indices, value)` nested array types, and `Arrays.select` and
  `Arrays.store` the selections `a[i][j]` and updates
  `a[i := a[i][j := v]]` of `a[i, j]` and `a[i, j := v]`. `state.exprs.lams`
  curries; the Boogie frontend reads and prints maps of several indices this
  way, SMT-LIB rejects lambdas of several variables (z3's multi-index arrays
  are not curried), Dafny does not print lambdas.
  The simplifier binds the variables of a lambda like those of `let`
  (renamed apart, without polarity), reduces `(λx. e)[t]` to `e[x := t]`
  (`select`) and the application of a function lambda likewise (`app`), also
  of arrays and function values defined by a lambda, `λx. a[x]` to `a` and
  `(x, y) => f(x, y)` to `f` (`lam`, eta), and an equation of two lambdas
  to `forall x, y :: e == e'` (`eq_`, extensionality); the equation of an
  array or function value and a lambda is kept, since it defines it.

- **Traversals:** `expr.map(f)` applies `f` to the immediate subexpressions
  point-wise and keeps bound variables, likewise `upd.map(f)`,
  `sort.map(f)`, `attrs.map(f)`, `prog.map(e, p)` (expressions, attributes,
  and immediate subprograms), and `cmd.map(e, p)`; `prog.subprogs` lists the
  immediate subprograms. There is no `subexprs`: to visit the subexpressions,
  call `expr.map` for its side effect and return the argument unchanged.
  Traversals that rename bound variables, e.g. `Subst`, are written out.
- **`Match`** has linear patterns built from constructors and variables
  (checked by `Type.check`); the patterns are not visited by `map` and not
  substituted, their variables are renamed if they would capture. Conditions
  of cases are not SMT-LIB, where they are `true`.
- **`Rec`** is a recursive function value of type `Arrow(fun.args, fun.res)`,
  like a lambda that may call itself, internal only (no syntax, the printers
  reject it). `fun` is bound in the cases; recursive calls are `App(fun, ...)`.
  Each pattern applies `fun` to linear patterns of its arguments, the
  conditions are guards, and the first case that matches and whose guard holds
  applies. The type parameters of `fun` are bound too: rigid in the cases and
  instantiated freshly at each use (`Type.check`), excluded from `Rec.params`,
  not substituted, and renamed if they would capture. The other types of `fun`
  may refer to those of the context, hence `Subst`, `Old.instance`, and
  `Type.expand` map them and the recursive calls with them (`Rec.retype`),
  since a function is identified by its types. The simplifier simplifies the
  cases like those of `Match` and does not unfold the function.
  `Rec.from(state, fun, body)` translates a definition: a body that matches
  on a formal parameter gives one case per case of the match, with the pattern
  in place of the parameter, also in the body and guard, and the other
  parameters renamed apart from the pattern variables; another body gives
  the single case `fun(xs) => body`. `Rec.from(state, fun)` looks up the
  definition in the state.
- **`App.inst`** holds the expected types of the arguments, not the
  instances of the type parameters. `App(fun, args)` computes `inst` and
  `typ` from the arguments.
- **Literals:**
  - integers are `BigInt`;
  - reals are exact [`util.Rational`](../src/util/Rational.scala), printed
    as decimals when finite, otherwise as fractions;
  - strings are `String`.
- **`Diff(xs, e)`** is a derivative, see [hybrid.md](hybrid.md).
- **`Old(e)`** never reaches the solver. `Old.elim(gs, gs_, ...)` replaces
  it by `e[gs := gs_]` before verification.
- **Trace combinators** `Trace`, `Maps`, `Invs`, whose updates are
  expressions, guarded ones as `Eps` of cases `Upd`, are described in
  [teq.md](teq.md). The guards of an update are disjoint and complete, which
  transformations may rely on.
- **Sugar.** [Builtin.scala](../src/cuvee/core/Builtin.scala) provides
  objects that both build and match applications of built-in functions:
  - `True`, `False`, `Eq`, `Ite`, `Not`, `And`, `Or`, `Imp`, `All`, `Ex`,
    `Select`, `Store`;
  - arithmetic per numeric type, `Ints.plus`, `Reals.plus`, `Reals.lt`, ...,
    the constants `Ints.zero` and `Reals.one`, and the rings `Ints.ring` and
    `Reals.ring` (see `Ring`);
  - the constructors of the datatypes of `core.dfy` of the lemma database, `Nats.zero`, `Nats.succ`,
    `Lists.nil(elem)`, `Lists.cons`, `Traces.stop`, `Traces.step`, and the
    tuples of the prelude of Dafny, `Tuples(args)`.

  The n-ary objects (`And`, `Ints.plus`, ...) flatten nested applications
  when matching.
- **Overloading.** The preludes declare arithmetic and comparison
  generically, e.g. `+ <a>(a, a): a`. After type checking,
  [`Overload`](../src/cuvee/core/Overload.scala) replaces each application
  by the implementation for its argument type:
  - `Fun.int.plus` or `Fun.real.plus`;
  - `seq.++` for `+`, and `seq.prefixof` for `<=`, on sequences.

  `select` and `store` (Dafny's `s[i]` and `s[i := v]`) are overloaded in
  the same way for arrays, sequences, and maps, membership `in` for sequences,
  sets, multisets, and maps (dispatched by its second argument). Maps
  (`Fun.map`, sugar `FinMaps`) are not expected to be supported by the
  solvers, and the
  generic `-` takes a second argument of another type for `m - s`.
  Each implementation is a single function of `Fun`, where those that are
  not part of cvc5 are added, e.g. `seq.member` for `x in s`, `seq.store`
  for `s[i := v]`, `map.store` for `m[k := v]`, and the proper orders
  `seq.proper_prefixof`, `set.proper_subset`, `bag.proper_subbag`; the
  solvers do not accept these yet (see TODO.md). `Type.check` records the
  applications of overloaded operators as pending constraints (a `Ref`
  threaded through checking), which are decided once the dispatch type is
  known, each exactly once, until no further one is decided; the remaining
  ones are reported as ambiguous. The implementations are pairs of a
  signature and a function, grouped by sort constructor like the functions,
  `Overload.bool`, `.int`, `.real`, `.array`, `.seq`, `.set`, `.bag`, and
  `.map`. Their signatures carry the name of the operator as in Dafny, e.g.
  `Overload.seq.concat` has the signature `+(Seq a, Seq a): Seq a` and the
  function `seq.++` (`Overload.overload`).
  `Overload.table` is derived from the signatures, keyed by operator name,
  arity, and the sort constructor of the dispatch argument. The generic
  operators never leave the frontend.

## Programs ([Prog.scala](../src/cuvee/core/Prog.scala))

```scala
sealed trait Prog { def mod: Set[Var]; def free: Set[Var] }

case object Break; case object Continue; case object Return
case class Spec(xs: List[Var], pre: Expr, post: Expr)   // assert pre; havoc xs; assume post
case class Assign(lhs: List[Var], rhs: List[Expr])      // parallel assignment
case class Call(proc: Name, args: List[Expr], res: List[Var])
case class Block(locals: List[Var], progs: List[Prog])
case class Choice(progs: List[Prog])                    // nondeterministic choice
case class If(test: Expr, left: Prog, right: Prog)
case class While(test: Expr, body: Prog, attrs: Attrs)  // invariant, decreases, modifies
case class Iter(body: Prog, attrs: Attrs)               // while * { body }
case class Ode(time: Var, xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs)
case class Par(progs: List[Prog])                       // parallel composition
```

- **`Spec`** covers `assert`, `assume` and `havoc`, through
  `Spec.assert(phi)`, `Spec.assume(phi)` and `Spec.havoc(xs)`.
- **`mod`** is the set of assigned variables. Global variables modified by
  calls are not included; they come from the callee's `modifies` attribute.
- **Modifies clauses.** `Type.check` takes the global variables that the
  enclosing procedure may modify. A loop modifies the global variables in its
  `modifies` attribute only, which must be modifiable outside of the loop and
  subsume the global variables that its body assigns, that calls in it modify,
  and the history that differential equations tick. Hence `VCGen` and `TEQ`
  take the modified variables of a loop as its `mod` and its `modifies`
  attribute. The C frontend infers the attribute of loops, the others require
  it in the input (`while ... modifies g` in Dafny, `modifies g;` in Boogie).
- **`free`** includes the variables in the attributes, e.g. in loop
  invariants.
- **`Ode`**, **`Iter`**, **`Par`**, `Send`, `Recv`, and `Tick` are hybrid programs and
  parallel composition, see [hybrid.md](hybrid.md).
- **`Sugar.call(name, in, out)`** builds and matches calls of a procedure with
  `in` arguments and `out` results, like the sugar of functions; `Send`,
  `Recv`, and `Tick` are instances.

```scala
case class Proc(name: Name, params: List[Param], in: List[Var], out: List[Var])
```

A procedure's inputs are fixed (never assigned), and its outputs are
results. The contract lives in the procedure's attributes in the `State`:
`requires`, `ensures`, `modifies`, `decreases`, `assumes`, `commits`.

## Attributes ([Attrs.scala](../src/cuvee/core/Attrs.scala))

```scala
case class Attrs(attrs: List[(String, Option[Any])])
```

An ordered list of keywords with optional values, as in SMT-LIB annotations.
The parsers store resolved values in them: `Expr` for `invariant` and
`requires`, and `List[Var]` for `modifies`. `values[T](kw)` reads all values
of one keyword with a given type. The accessors `requires`, `ensures`,
`modifies`, `decreases`, `invariants`/`invariant`, `assumes` and `commits`
read the contracts.

## Commands ([Cmd.scala](../src/cuvee/core/Cmd.scala))

```scala
sealed trait Cmd
sealed trait Decl extends Cmd     // changes the state
sealed trait Query extends Cmd    // asks for a result: CheckSat, GetModel, ...
sealed trait Ctrl extends Cmd     // Push, Pop, Reset, Exit, Done
```

- Declarations:
  - `DeclareSort`, `DefineSort`, `DeclareDatatypes`;
  - `DeclareFun`, `DefineFun`;
  - `DeclareVar` (global variables);
  - `DeclareProc`, `DefineProc`;
  - `Assert(justify, params, phi, attrs)`, where `justify` is `Axiom`,
    `Goal` or `Lemma`, and `params` are the type parameters, those declared
    by `lemma name<a>(...)` (Dafny) or `lemma <a> ...` (Boogie) followed by
    those that remain in `phi`; Dafny lemmas are named by the attribute
    `:named`;
  - `FuseFuns(term, rhs, attrs)`, the request `fuse g(f(xs), ys) = ???` of
    Dafny input to fuse two defined functions, whose `rhs` the stage `Fuse`
    (`-fuse`) sets to the fused `Rec` with the parameters `xs` and `ys`; it
    declares nothing, the Dafny printer prints the `Rec` as `function h(...) { case ... }`,
    which is not parsed, the other printers reject it.
- `Datatype(params, constrs)` lists each constructor with its selectors.
  Dafny qualifies the selectors with the datatype, e.g. `event_chan`;
  Boogie, whose datatypes are written like Dafny's with the keyword `data`
  (`data Stack<a> = empty | push(top: a, pop: Stack<a>);`, not Boogie),
  does not, since it has no member access, so its selectors are unique
  functions as in SMT-LIB.
- Mutually recursive datatypes are one `DeclareDatatypes`, as in SMT-LIB.
  Boogie joins them by `and` in one `data` command,
  `data Tree<a> = ... and Forest<a> = ...;`. Dafny reads a run of
  consecutive `datatype` declarations together, which may refer to each
  other and to later ones, and declares each strongly connected component
  as one group, after those that it refers to (`Parser.groups`); its
  printer writes the datatypes of a group one after another.
- `Done` is internal: it marks the end of the input, so that the stages
  flush.
- Results:
  - `Ack` (`Success`, `Unsupported`, `Done`);
  - `Status` (`Sat`, `Unsat`, `Unknown`);
  - `Model`, `Info`, `Value`, `Labels`;
  - `cuvee.Error`.

## State ([State.scala](../src/cuvee/core/State.scala))

```scala
case class State(
  sorts, funs, vars, procs,                     // declarations by name (funs by name and arity)
  sortattrs, funattrs, varattrs, procattrs,     // their attributes
  sortdefs, fundefs, procdefs, datatypes,       // their definitions
  logic, options, infos)
```

- `State.add(decl)` returns the state extended by a declaration.
- The builders are used by all frontends:
  - `state.types.sort(name, args)`;
  - `state.exprs.app(name, args)`, which instantiates the type parameters
    freshly, and `state.exprs.app(fun, args)` for built-in functions that
    are not declared;
  - `state.exprs.check`;
  - `state.progs.*`, which build programs and check them.
- `state.globals` are the declared global variables.

`Scope(params, vars)` is the local context while resolving and type
checking: the type parameters and the variables, by name.

## Substitutions ([Subst.scala](../src/cuvee/core/Subst.scala))

```scala
case class Subst[T <: Type, E <: Expr](params: Map[Param, T], vars: Map[Var, E])
```

- A substitution replaces type parameters and variables at the same time,
  in types, expressions, attributes and programs.
- It avoids capture under binders and blocks by renaming bound variables
  (`avoid`).
- Assigned variables and the variables of derivatives can only be renamed
  (`lhs`).
- Constructors:
  - `Subst.from(xs, es)`;
  - `Subst.fresh(params)` and `Subst.fresh(vars)`;
  - `Subst.rename(xs)` returns fresh copies of `xs` with the renaming to
    them, `Subst.rename(xs, avoid)` renames only those that clash with
    `avoid` by name. Transforms that need fresh bound variables use these,
    rather than renaming by hand.
- `x.fresh` returns a copy with a new index from a global counter.
  `Var.reset()` and `Param.reset()` make the numbering deterministic per
  run.

## Simplifier

The data structures of the simplifier (`Context`, `Poly`, `Constraint`,
`Rule`) and fusion (`Fuse`) are described in [simplifier.md](simplifier.md).
