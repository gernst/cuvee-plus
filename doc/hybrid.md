# Hybrid programs and parallel composition

Non-standard extensions of the Dafny frontend after Platzer's differential
dynamic logic (dL), and parallel composition with assumption-commitment
contracts (see [examples/dafny/hybrid/](../examples/dafny/hybrid): `ball.dfy`,
`clock.dfy`, `newton.dfy`, and `par.dfy`). Derivatives,
differential equations, and nondeterministic iterations are always part of
the Dafny frontend; the option `-hybrid` is needed for parallel composition
only, it injects [hybrid.dfy](../resources/cuvee/dafny/hybrid.dfy), which
declares the polymorphic datatype `history<a₀>` of event sequences with the
methods `send`, `receive`, and `tick`. An event is a message
`message(chan, value)` or the passing of time `time(time: real)`.
`project(c, h)` are the values of the messages on `c` in `h`; `delay(h, t)`
appends the passing of `t` time units to `h`, merged with a last time event,
and nothing for `t == 0`. `history.tick(t)` extends the history by
`delay`. The input declares the global variable
`history` of an instance, e.g. `var history: history<int>`.

## Syntax

| Construct | Dafny frontend | dL |
|---|---|---|
| derivative | `(x, v :: 2.0 * g * x + v * v)'` | `(2 g x + v²)'` |
| differential equation | `ode t :: x', v' == v, -g while 0.0 <= x invariant φ;` | `{t' = 1, x' = v, v' = -g & 0 ≤ x}` |
| iteration | `while * invariant φ { body }` | `body*` |
| parallel composition | `parallel { x := p(a); q(b); }` | |
| contracts | `assumes φ` and `commits ψ` after `ensures` | |

- A differential equation is a statement: the keyword `ode`, the time
  variable, `::`, the primed variables, `==`, the right-hand sides in the
  same order, optionally `while` and the evolution constraint, then the
  differential invariants, and a semicolon, e.g.

  ```dafny
  ode t :: x', v' == v, -g while 0.0 <= x
    invariant 2.0 * g * x + v * v <= 2.0 * g * h;
  ```

  The time `t` is bound by `ode` on `real` (it is not declared), and
  available in the right-hand sides, the constraint, and the invariants. The
  keyword `ode` avoids backtracking against assignments and calls.
- `while *` is a loop with a nondeterministic number of iterations; `if *`
  is a nondeterministic choice.
- In a derivative `(xs :: e)'`, the variables `xs` are those that `e` is
  differentiated with respect to; the result refers to their primed versions
  `x'`.
- `parallel { ... }` composes statements, of which verification supports
  calls only, written as call statements or as assignments of their results.

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
case class Ode(time: Var, xs: List[Var], rhs: List[Expr], dom: Expr, attrs: Attrs)
case class Iter(body: Prog, attrs: Attrs)               // while * { body }
```

- `Ode` is the system `x' = e` for `x` in `xs` with the evolution constraint
  `dom` (`True` if there is none). Its `invariant` attributes are the
  differential invariants. The variables are on `Real`. The time is a bound
  variable on `Real` (renamed by `Subst` like those of binders), neither free
  nor modified. In SMT-LIB, it is `(ode t ((x e) ...) dom attrs)`.
- `Iter` is the repetition of dL, a loop with a nondeterministic number of
  iterations.
- `VCGen` proves an `Ode` by differential cuts with its invariants, then
  weakening, where the time starts at `0.0` and evolves with `time' = 1`
  within `0 <= time`. Afterwards, if the global `history` is declared, it
  ticks by the time that has passed, `history := history.tick(time)`
  (`VCGen.tick`), which asserts the enclosing commitment like `Tick`. Hence
  an `Ode` modifies the history, which must be in the modifies clause of the
  method and of loops around it (`Type.check`). The derivatives of the
  invariants must be simplified
  (`-prove`) before the goals can be passed to a solver.

## Parallel composition

```scala
case class Par(progs: List[Prog])                       // parallel composition
```

- `-vcgen` supports calls only and rejects other statements (`VCGen`).

- The callees' contracts `assumes` and `commits` (procedure attributes) are
  formulas over the shared history, the global variable named `history`
  (`State.history`), whose events are `history.events`.
- The programs must not share modified variables other than the history
  (`Par.shared`, type checking).
- `history := history.send(c, v)`, `x, history := history.receive(c)`, and
  `history := history.tick(t)` call the methods of the datatype, i.e. the
  procedures `history_send`, `history_receive`, and `history_tick` with the
  history as first argument, which return the extended history as an
  additional result. `Send`, `Recv`, and `Tick` recognize
  these calls; in `VCGen`, each one asserts the enclosing procedure's
  commitment for the extended history and then assumes it. Calls to
  polymorphic procedures instantiate their contracts by the types of the
  arguments and results (`Type.bind`).
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
- `VCGen` has a rule `par` (assumption-commitment), which knows the
  assumption and commitment of the enclosing procedure (parameters `assume`
  and `commit` of `wp`): the commitments of the calls must hold initially,
  the enclosing assumption and the commitments of the other calls must imply
  the assumption of each call, and the commitments of the calls must imply
  the enclosing commitment, both for all histories. Each call is a process
  that starts in the current state and is verified modularly by its contract
  (`VCGen.instance`, as for calls): its precondition must hold initially,
  and its body is not considered. Afterwards,
  the results of each call satisfy its postcondition, over a copy of the
  history of its own, and the history is arbitrary, satisfying all
  commitments. `Horn` and `-teq` do not support parallel composition.
