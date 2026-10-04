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
- `Name.primed` appends `'`; derivatives use it.

## Types ([Type.scala](../src/cuvee/core/Type.scala))

```scala
case class Con(name: Name, arity: Int)          // sort constructor, e.g. Array/2
sealed trait Type
case class Param(name: Name) extends Type       // type parameter
case class Sort(con: Con, args: List[Type]) extends Type
```

- Built-in sorts:
  - `Sort.bool`, `Sort.int`, `Sort.real`, `Sort.string`;
  - `Sort.array(dom, ran)`, `Sort.seq(elem)`.
- Defined sorts (`define-sort`, Dafny `type T = ...`) are unfolded on
  demand by `Type.unfold`.
- `Type.unify` drives type checking. It respects rigid parameters: those of
  the enclosing declaration, kept in the `Scope`.
- `Type.bind` matches a signature against argument types.

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
case class Let(bound: List[Var], args: List[Expr], body: Expr)
```

- **`App.inst`** holds the expected types of the arguments, not the
  instances of the type parameters. `App(fun, args)` computes `inst` and
  `typ` from the arguments.
- **Literals:**
  - integers are `BigInt`;
  - reals are exact [`util.Rational`](../src/util/Rational.scala), printed
    as decimals when finite, otherwise as fractions;
  - strings are `String`.
- **`Diff(xs, e)`** is free in `xs`, which are ordinary variables without
  primes, and must be on `Real`. Primed variables `x'` for the derivatives of
  `xs` appear only once the simplifier computes the derivative.
- **`Old(e)`** never reaches the solver. `Old.elim(gs, gs_, ...)` replaces
  it by `e[gs := gs_]` before verification.
- **Sugar.** [Builtin.scala](../src/cuvee/core/Builtin.scala) provides
  objects that both build and match applications of built-in functions:
  - `True`, `False`, `Eq`, `Ite`, `Not`, `And`, `Or`, `Imp`, `All`, `Ex`,
    `Select`, `Store`;
  - arithmetic per type, `Plus.int`, `Plus.real`, `Lt.real`, ...;
  - constants `Zero.int` and `One.real`.

  The n-ary objects (`And`, `Plus.int`, ...) flatten nested applications
  when matching.
- **Overloading.** The preludes declare arithmetic and comparison
  generically, e.g. `+ <a>(a, a): a`. After type checking,
  [`Overload`](../src/cuvee/core/Overload.scala) replaces each application
  by the implementation for its argument type:
  - `Fun.int.plus` or `Fun.real.plus`;
  - `seq.++` for `+`, and `seq.prefixof` for `<=`, on sequences.

  `select` and `store` (Dafny's `s[i]` and `s[i := v]`) are overloaded in
  the same way for arrays and sequences. The type checker picks the
  implementation (`Impl`) as soon as the type of the first argument is
  known, and checks the application against its signature. The generic
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
case class Ode(xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs)
case class Par(calls: List[Call])                       // parallel composition of calls
```

- **`Spec`** covers `assert`, `assume` and `havoc`, through
  `Spec.assert(phi)`, `Spec.assume(phi)` and `Spec.havoc(xs)`.
- **`mod`** is the set of assigned variables. Global variables modified by
  calls are not included; they come from the callee's `modifies` attribute.
- **`free`** includes the variables in the attributes, e.g. in loop
  invariants.
- **`Ode`** is the system `x' = e` for `x` in `xs` with evolution constraint
  `dom`. Its `invariant` attributes are the differential invariants. The
  variables are on `Real`.
- **`Par`** composes calls in parallel:
  - The callees' contracts `assumes` and `commits` are formulas over the
    shared history, the global variable named `history`.
  - The calls must not share modified variables other than the history
    (`Par.shared`).
- **`Send(chan, value)` and `Recv(chan, x)`** are sugar for calls to the
  procedures `send` and `receive`, which extend the history. In `Verify`,
  each one asserts the enclosing procedure's commitment for the extended
  history and then assumes it.

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
    `Goal` or `Lemma`.
- `Datatype(params, constrs)` lists each constructor with its selectors.
  Dafny qualifies the selectors with the datatype, e.g. `event_chan`.
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
  asserts, logic, options, infos)
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
  - `Subst.fresh(params)` and `Subst.fresh(vars)`.
- `x.fresh` returns a copy with a new index from a global counter.
  `Var.reset()` and `Param.reset()` make the numbering deterministic per
  run.

## Simplifier ([simplify/](../src/cuvee/simplify))

- **`Ctx`** is a sequent at the current position:
  - assumptions and conclusions;
  - bound variables;
  - equalities between variables, as a substitution;
  - the polarity of the position, and whether the context is inconsistent.
- **`Poly(const, monos)`** with `Mono(factor, atoms)` is the normal form of
  arithmetic, with `Rational` coefficients. `Ring` bundles the sugar of one
  type (`Ring.int`, `Ring.real`) to read and print polynomials.
- **`Poly.sides`** splits a polynomial into its negative and positive parts,
  so that comparisons have positive coefficients on both sides.
- **`Constraint(poly, strict)`** is a linear constraint `0 <= poly` or
  `0 < poly`. `FourierMotzkin` eliminates atoms from conjunctions of these and
  decides their satisfiability over the rationals.
- **`Rule(lhs, rhs, cond)`** is a conditional rewrite rule, whose variables
  are the free variables of `lhs`. `Rewrite` rewrites innermost first,
  matching modulo type instantiation, A/C and 0 of `+` and `-`, and the
  binding structure of `Trace`, `Maps`, and `Invs` (dependencies of
  the pattern that are variables are instantiated by `map` expressions).
