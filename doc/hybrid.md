# Hybrid programs and parallel composition

Non-standard extensions of the Dafny frontend after Platzer's differential
dynamic logic (dL), and parallel composition with assumption-commitment
contracts (see [examples/dafny/hybrid.dfy](../examples/dafny/hybrid.dfy) and
[examples/dafny/par.dfy](../examples/dafny/par.dfy)). The option `-hybrid`
injects [hybrid.dfy](../resources/cuvee/dafny/hybrid.dfy), which declares the
history, `send`, and `receive`.

## Derivatives

```scala
case class Diff(xs: List[Var], expr: Expr)     // derivative (xs :: expr)'
```

- `Diff(xs, e)` is free in `xs`, which are ordinary variables without primes,
  and must be on `Real`.
- Primed variables `x'` (`Name.primed`) for the derivatives of `xs` appear
  only once the simplifier computes the derivative (`Simplify.diff`, by the
  rules of dL); what has no rule is kept as `Diff`.

## Differential equations

```scala
case class Ode(xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs)
case class Iter(body: Prog, attrs: Attrs)               // while * { body }
```

- `Ode` is the system `x' = e` for `x` in `xs` with the evolution constraint
  `dom`, written `{x' = e, y' = f & dom}` in dL. Its `invariant` attributes are
  the differential invariants. The variables are on `Real`.
- `Iter` is the repetition of dL, a loop with a nondeterministic number of
  iterations.
- `Verify` proves an `Ode` by differential cuts with its invariants, then
  weakening; the derivatives of the invariants must be simplified
  (`-simplify`) before the goals can be passed to a solver.

## Parallel composition

```scala
case class Par(calls: List[Call])                       // parallel composition of calls
```

- The callees' contracts `assumes` and `commits` (procedure attributes) are
  formulas over the shared history, the global variable named `history`
  (`Par.history`).
- The calls must not share modified variables other than the history
  (`Par.shared`).
- `Send(chan, value)` and `Recv(chan, x)` are sugar for calls to the
  procedures `send` and `receive`, which extend the history. In `Verify`,
  each one asserts the enclosing procedure's commitment for the extended
  history and then assumes it.
  - Communication is always joint: the event of a `receive` is the event of
    the matching `send` of another process, and both extend the same history.
    Hence a process commits first, also after receiving: the commitment must
    hold for the extended history before the process relies on anything about
    the new event.
  - A commitment must always be made before an assumption is taken. The
    assumption of a process is justified by the commitments of the other
    processes (rule `par`), which hold for every history that they produce.
    Inside the body, it is therefore taken only initially, and the new event
    of a `receive` is constrained by the contract of `receive` only.
- `Verify` has a rule `par` (assumption-commitment); `Horn` and `-teq` do not
  support parallel composition.
