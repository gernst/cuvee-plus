# Proving trace lemmas

Status: proposal. The definition of traces and the unfolding of the
combinators are tried in an experiment,
[teq-def.dfy](../resources/cuvee/teq-def.dfy) (section 1); nothing else is
implemented. The lemmas of
[teq.dfy](../resources/cuvee/teq.dfy) and
[teq-new.dfy](../resources/cuvee/teq-new.dfy) are trusted (`{:free}`). The new
ones are checked only by examples, unsafe variants, and mutants (see
[examples/sv-comp/summary.md](../examples/sv-comp/summary.md)). This note
proposes:

- proving them by induction over traces, with a small proof script or an
  automatic tactic;
- treating that induction as an instance of induction over data types;
- deriving lemmas instead of writing them: the acceleration lemmas of the
  functions that introduction lemmas name, by fusion of the observers with
  the trace combinator, in the unfold/fold style.

## 1. The combinators as recursive definitions

The combinators are folds over their dependencies. `Trace` and `seq` have no
definition in teq.dfy, where `Trace` is declared only. A trace is a
non-empty sequence, defined as a data type that is taken apart at its last
element:

```
datatype Trace<a> = Stop(value: a) | Step(init: Trace<a>, last: a)
```

Taking it apart at the end fits counters. They start at a fixed value,
usually 0, but have an arbitrary number of steps `n`, so an induction over
`n` unfolds `counter(i, c, n + 1)` at its end. Read front to back, i.e., by
`ys + [y]`, the combinators and observers are defined by these equations,
with `F` and `P` the update and the condition as higher-order variables:

```
trace(x0, for [] do x, z :: F(x, z))          == Stop(x0)
trace(x0, for ys + [y] do x, z :: F(x, z))    == Step(T, F(current(T), y))
                                                 where T = trace(x0, for ys do x, z :: F(x, z))
maps(for [] yield z :: F(z))                  == []
maps(for ys + [y] yield z :: F(z))            == maps(for ys yield z :: F(z)) + [F(y)]
invs(for [] check z :: P(z))                  <==> true
invs(for ys + [y] check z :: P(z))            <==> invs(for ys check z :: P(z)) && P(y)
counter(i, c, 0)                              == Stop(i)
counter(i, c, n + 1)                          == Step(counter(i, c, n), i + (n + 1) * c)   for 0 <= n
current(Stop(x)) == x,   current(Step(T, x)) == x
⌊Stop(x)⌋ == [],         ⌊Step(T, x)⌋ == ⌊T⌋ + [current(T)]
```

The same holds for several dependencies of equal length, point-wise. The
`case` updates are conditionals in `F`. The observers `earlier`, `prefix`,
`selects`, `occurs`, `indexof`, `distincts` and `count` are recursive
functions on sequences in the same way, e.g.
`count(e, vs + [v]) == count(e, vs) + (if v == e then 1 else 0)`.

These equations are the semantics of the paper (sec. 3). They make every
lemma of the database a theorem about recursive functions on traces and
sequences. The point is to apply them only where a proof needs them, see
section 3.

### The experiment teq-def.dfy

[teq-def.dfy](../resources/cuvee/teq-def.dfy) states these definitions in
Dafny, run with `-simplify`. It is not used with `-teq`, since both declare
`Trace`.

- **The data type:** a data type named `Trace` coincides with the sort of
  the combinators (`Sort.trace`), so `trace(...)` has this type, and lemmas
  about the data type may use the combinators.
- **No built-in unfolding needed:** the unfolding of `trace`, `maps` and
  `invs` is expressible as rewrite rules in the language, with
  higher-order patterns for the updates and conditions, and dependencies
  `ys + [y]`.
- **Observers:** `current` and `butlast` are definitions with a top-level
  `match` and `{:rw}`.
- **`counter`:** a recursive definition, not a rewrite rule, since it
  would unfold for a variable `n` without end. Two lemmas unfold it at `0`
  and at `n + 1`.
- **One lemma per number of dependencies,** since a pattern has a fixed
  number of them; the experiment has one and two.
- **The checks pass:** generic in `F` and `P`, polymorphic, closed by
  `-simplify`, for one dependency, for a counter, and for the synthetic
  counter with a second dependency, e.g.
  `current(trace(x0, for ys + [y] do x, z :: F(x, z))) == F(current(trace(x0, for ys do x, z :: F(x, z))), y)`.
- **The first derived lemma:** the unfolding of `⌊counter(i, c, n + 1)⌋`
  needs `current(counter(i, c, n)) == i + n * c`. It follows from the
  definition by induction, and is stated as a lemma there.
- **Limitations, which are acceptable:**
  - Expressions are compared literally, not modulo the names of bound
    variables. The checks use the names of the lemmas, and with a concrete
    update that does not use a dependency, the simplifier drops it, after
    which the names differ (see TODO.md).
  - Sequences still have no definition. They are those of SMT-LIB, taken
    apart by the patterns `[]` and `ys + [y]`, so the unfolding matches
    only dependencies of these forms, which an induction introduces.

## 2. Two styles of proof

### Point-wise (extensional) reasoning

A trace or sequence is determined by its length and its elements:

```
X == Y  <==>  |X| == |Y| && forall j :: 0 <= j < |X| ==> earlier(j, X) == earlier(j, Y)
```

A lemma is proved by computing `earlier(j, ...)` of both sides. This works
where an element at `j` depends on the dependencies at `j` only:

- for `maps` and `invs`, e.g. the abstractions `invs(... earlier(k, xs) == earlier(k, ys)) <==> agree(n, xs, ys)`;
- for reads of `stores` at distinct keys, e.g. the guarded store at
  position `j`;
- for `occurs` over counters and the lengths of counters.

It does not help for `trace` itself. The element at `j` is defined by the one
at `j - 1`, so the point-wise characterization of a trace is a recurrence,
and solving it is the induction below. Point-wise reasoning is also the
fallback of the paper for SMT (sec. 5.3), with quantifiers, which the
simplifier does not instantiate.

### Induction over the trace, front to back

Most lemmas state a closed form of an observer of a trace:

```
current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: U(x, k)))  ==  C(x0, n)
```

The proof is by induction over `n`, i.e., over the dependencies by `ys + [y]`:

1. **Base** `n == 0`: unfold `trace` over `[]`, which gives `x0 == C(x0, 0)`.
   The simplifier decides it.
2. **Step** `n + 1` with `0 <= n`:
   - Unfold `counter(0, 1, n + 1)` and `trace` once; then
     `current(...) == U(current(T_n), n)`.
   - Rewrite `current(T_n)` by the induction hypothesis to `C(x0, n)`.
   - The remaining goal is `U(C(x0, n), n) == C(x0, n + 1)`, i.e., the closed
     form is a fixpoint of the update. It is decided by the simplifier, with
     `-split` for the cases of `U` and of `C`.

For example, the two phases of `phases_1-1`:
`U(x, k) = if x < b then x + 1 else x + c` and
`C(x0, n) = if n <= b - x0 then x0 + n else b + (n - (b - x0)) * c`.

- The step has the four cases of the two conditionals. With `x0 <= b`,
  each is linear arithmetic.
- The case `n == b - x0`, where `C` switches to the second phase, is the
  only one that needs `x0 + n == b`.

The lemmas of the database fall into a few patterns:

| pattern | examples | induction |
|---|---|---|
| closed form of `current` | counters, phases, follower, geometric, flags | as above |
| closed form of a read `current(...)[j]` | recurrences, guarded stores, clamps | as above, with `j` universally quantified in the hypothesis |
| invariant of `current` | interval, modular, positive increments | hypothesis `P(current(T_n))`, step `P(x) ==> P(U(x))`, which are the side conditions of the lemma |
| equivalence of `invs` | bounds of counters, the bound at the last value | unfold `invs` and the counter, monotonicity as an auxiliary lemma |
| abstraction and instantiation | `agree`, `absent`, `!occurs(e, prefix(n, xs))` | definitional; the instantiation is point-wise, or by induction over `n` with the case `j == n` |
| counts | remainders, complements | induction over `n`, arithmetic of `div` and `mod` in the step |
| arithmetic | parity, halving, telescoping | no traces, see below |

Three things are needed beyond the recipe:

- **Generalization:** quantify over the parameters that the step changes,
  e.g. the read position `j`, and the initial value of a follower. The
  induction is then over a lemma that is more general than the one stated.
- **Auxiliary lemmas:**
  - monotonicity of a two-phase counter, for its bound at the last value;
  - `prefix` and `earlier` over `ys + [y]`;
  - reads of stores.

  These are proved first and used as rules.
- **Arithmetic side goals:**
  - nonlinear identities, e.g. telescoping with `(k + 1)^3`;
  - `div` and `mod`, e.g. `(m * k + r) / m == k`.

  The simplifier normalizes polynomials, but does not round and does not
  case-split on `mod`. These obligations contain no traces, hence an SMT
  solver could discharge them, as plain integer arithmetic in a separate
  file, if the restriction to keep solvers away from `-teq` output (see the
  notes) is read as concerning trace goals only. That is to be decided.

## 3. Proof scripts and an automatic tactic

### A proof script

A lemma names its induction and its steps:

```
lemma {:rw} {:teq} {:by "induct n; unfold; ih; split; simplify"}
  forall x0: int, n: int, b: int, c: int ::
    if x0 <= b
    then current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c))
           == if n <= b - x0 then x0 + n else b + (n - (b - x0)) * c
```

- `induct n` produces the two goals with `n == 0` and `n + 1` and the
  hypothesis for `n`, generalized over the variables given, e.g.
  `induct n generalizing j`.
- `unfold` applies the equations of section 1 once, at the terms that
  contain `n + 1` or `[]`.
- `ih` adds the induction hypothesis as a rewrite rule.
- `split; simplify` are the existing transforms on the obligation.

Lemmas proved so far are rules of later proofs, in the order of the file. A
lemma without `{:by ...}` stays `{:free}`. The output is the remaining
goals, as with `-simplify`. A failed step is reported with its goal.

### An automatic tactic

The script is the default, which a tactic tries without annotation:

- **Induction variable:** the length of the counter among the dependencies
  of the trace of the left-hand side, e.g. `n` of `⌊counter(i, c, n)⌋`, or
  the sequence variable of a dependency, by `ys + [y]`.
- **Generalization:** over the variables of the lemma that occur in the
  observer but not in the trace, e.g. `j` of a read.
- **Search:** `unfold; ih; simplify`, then with `split`. If a goal remains,
  try once more with the auxiliary lemmas that the goal suggests:
  monotonicity for comparisons with `current`, and `earlier` over `prefix`.
- **Termination:** the unfolding lemmas of section 1 match only the shapes
  `[]`, `ys + [y]`, `0` and `n + 1` that the induction introduces, hence
  they terminate as rewrite rules. They are rules of proofs only, not of
  `-teq`, where they would turn traces into data. The definition of
  `counter` itself is no rule, since it would unfold for a variable `n`
  without end.

This would turn `teq-new.dfy` into proved lemmas, except for arithmetic,
which is left to the decision above. Failures point to wrong lemmas: a
mutated lemma leaves a goal of the step.

## 4. In perspective: induction over data types

Induction over traces is structural induction over the data type
`Trace = Stop | Step` of section 1, and induction over its dependencies is
induction over sequences by `ys + [y]`, i.e., over a data type
`Seq = [] | snoc(Seq, a)`. The same machinery serves user data types:

- **Recursive definitions:** `Rec` represents a recursive function with a
  top-level match and guards. `Rec.from` translates definitions with a
  top-level `match`.
- **Unfolding:** applying the case of a `Rec` whose pattern matches a
  constructor term, which `Fuse` already does when it drives a function
  into a constructor.
- **Induction schemas:** structural induction from the constructors of a
  `Datatype`, a hypothesis per recursive argument. For `nat`-like counters,
  `n == 0` and `n + 1` with `0 <= n`.
- **Traces** have constructors, by the data type of section 1, and
  `counter(i, c, n + 1)` unfolds to a `Step`.
- **Sequences** have no constructors in SMT-LIB. They get the views `[]`
  and `ys + [y]`, which the unfolding lemmas already use as patterns.

So the combinators need not be built in: they are lemmas over these
constructors and views, as in teq-def.dfy. `trace(x0, for deps do F)` is
the fold `trace_F(x0, deps)`, and `maps` and `invs` likewise. The tactic of
section 3 is structural induction over `Trace`, over sequences by their
views, and over `n` for counters. It is the same tactic as for lemmas about
user functions on lists, e.g. for the `fuse` examples. What remains to be
built in is the induction, not the unfolding.

## 5. Deriving acceleration lemmas by fusion

### Introduction lemmas as definitions

An introduction lemma names a fragment of a trace:

```
trace(x, for values do s, v :: s + v) == sums(x, values)
```

Read from right to left, it is the definition of `sums`, which teq.dfy only
declares. The acceleration lemmas then are theorems about this definition,
e.g. `current(sums(x, values)) == x + sum(values)`, and
`earlier(j, ⌊sums(x, values)⌋) == x + sum(prefix(j, values))`. Today each of
them is written and trusted. They can be derived instead.

### Fusing an observer with the fold

`current(trace(x0, for deps do F))` is a composition of two recursive
functions:

- `current`, with `current(Stop(x)) == x` and `current(Step(T, x)) == x`;
- the fold `trace_F`.

Fusion (`simplify/Fuse.scala`, `g(f(xs), ys)` into `h(xs, ys)`) drives
`current` into the cases of the fold:

```
trace_F(x0, [])        == Stop(x0)               ==>  h(x0, [])        == x0
trace_F(x0, ys + [y])  == Step(T, F(cur(T), y))  ==>  h(x0, ys + [y])  == F(h(x0, ys), y)
```

The result `h` is the plain fold `foldl(F, x0, deps)`, without
intermediate traces. This is deforestation of the trace, and the reason why
`current` of every introduced function has a closed form at all.

What `Fuse` needs for this:

- **Patterns of views** `ys + [y]` in place of constructors for sequences
  (section 4); the constructors `Stop` and `Step` of traces are ordinary.
- **Accumulator positions:** `current` applied to the recursive call
  `T = trace_F(x0, ys)` inside the result. This is the case `g(f(t), z)` that
  `Fuse` already turns into `h(t, z)`, here at an accumulator position.
- **Lets:** the value of `cur(T)`, which is `h(x0, ys)` again.

### Recognizing the result: unfold/fold

The fused `h` must be recognized as a known function or a closed form. This
is the fold step of unfold/fold, with a generalized accumulator:

- `h(x, [])         == x`
- `h(x, ys + [y])  == h(x, ys) + y`

`sum` is defined by `sum([]) == 0` and `sum(ys + [y]) == sum(ys) + y`.
The conjecture `h(x, ys) == x + sum(ys)` holds for `[]`, and is preserved by
the step: `h(x, ys) + y == x + sum(ys) + y == x + sum(ys + [y])`. Both are
goals of the tactic of section 3. The result is the lemma
`current(sums(x, values)) == x + sum(values)`, derived from the definition of
`trace` and the introduction lemma alone.

The other acceleration lemmas follow by the same scheme:

- **`earlier` and `prefix`:** one general lemma, proved once by induction:
  `earlier(j, ⌊trace(x0, for deps do F)⌋) == current(trace(x0, for prefix(j, deps) do F))`.
  The earlier-lemma of each introduced function is then its current-lemma
  instantiated at `prefix(j, deps)`, e.g.
  `earlier(j, ⌊sums(x, values)⌋) == x + sum(prefix(j, values))`.
- **`counts`, `parities`:** the fused fold is
  `h(x, ys + [y]) == h(x, ys) + (if y == e then 1 else 0)`, recognized as
  `x + count(e, ys)` by the definition of `count`.
- **`maxs`, `mins`:** `h(m, ys + [y]) == max(h(m, ys), y)`. There is no
  closed form; the derived lemmas are bounds: the initial value and each
  element are at most `current`. These invariants are proved by induction
  from the fused fold, not recognized.
- **Counters and constants:** recognition by a polynomial in `n`:
  `h(i, n + 1) == h(i, n) + c` gives `i + n * c`, a linear recurrence with
  constant coefficients, which can be solved by a template.

### Synthesizing derived lemmas

A procedure over the database:

1. For each introduction lemma `trace(x0, for deps do F) == f(x0, deps)`,
   take the right-to-left reading as the definition of `f`.
2. For each observer `o` in (`current`, `earlier(j, ⌊·⌋)`, `steps`, reads at a
   key), fuse `o ∘ trace_F` into a fold `h`.
3. Recognize `h`:
   - by matching its equations against definitions of known functions
     (`sum`, `count`, `max`), with a generalized accumulator: `h(x, ys)` as
     `x ⊕ g(ys)` for an operator `⊕` of the step;
   - or against templates of closed forms (polynomials in `n` for
     counters, geometric for products).
4. Prove the conjecture by the tactic, and emit it as a lemma
   `o(f(x0, deps)) == closed form`.
5. Emit the fused fold itself as a lemma if no closed form is found, since
   it still removes the intermediate trace, e.g. for `maxs`.

The same scheme applies to traces that are no introduction lemma yet,
which is how the lemmas of `teq-new.dfy` could be synthesized from the
programs instead of written:

- **A recurrence over an array:** e.g. `b[i := b[k] + G(k)]`. Fusing the
  read at `j` with the fold gives
  `h_j(b0, ys + [k]) == if k + 1 == j then h_k(b0, ys) + G(k) else h_j(b0, ys)`.
  The conjecture `h_j == b0[0] + sum(prefix(j, G))` is recognized by
  generalizing over `j`.
- **A two-phase counter:** the fused fold `h(x, n + 1) == U(h(x, n))` has no
  template. Its closed form needs a case split by phase, which a template
  `if n <= t then p₁(n) else p₂(n)` with an unknown threshold `t` could
  provide, solving for `t` from the guard.
- **Invariants:** an interval or modulus preserved by `U`, found by
  abstract interpretation of the fused fold, e.g. intervals and congruences
  as domains. The candidate is then proved by the tactic.

### Limits

- Recognition is incomplete: closed forms beyond polynomials and the known
  functions need user lemmas, and invariants need candidates.
- Fusion requires each step of the observer to depend on the previous
  value only, which holds for `current` and reads, not for `invs` over the
  whole trace, which is itself a fold, fused separately.
- The arithmetic of the proofs needs `div` and `mod`, see section 2.

## Plan

1. **Unfolding:** the equations of section 1 as lemmas over the data type
   `Trace`, done as an experiment in teq-def.dfy, for one and two
   dependencies. Missing: the observers `earlier`, `prefix`, `selects`,
   `count`, etc. over sequences, more dependencies, and a way to use these
   rules in proofs only.
2. **Induction:** the script `{:by ...}` for lemmas, with `induct`,
   `unfold`, `ih`, `split`, `simplify`; the lemmas of `teq-new.dfy` are the
   test cases, the mutants are failure cases.
3. **The tactic:** the default script with the heuristics of section 3.
4. **Fusion of observers:** `Fuse` with patterns of views and accumulator
   positions; `current ∘ trace` and reads.
5. **Recognition:** matching against definitions of `sum`, `count`,
   `max`, and templates of polynomials, with proofs by the tactic.
6. **Synthesis:** derive the acceleration lemmas of teq.dfy from its
   introduction lemmas, compare with the written ones, then the lemmas of
   the SV-COMP examples.

## Open questions

- Should the arithmetic obligations of lemma proofs go to an SMT solver?
  They contain no traces. Or should the simplifier learn rounding and
  `div`/`mod`?
- Should the introduction lemmas become definitions of the functions they
  name? Then those functions are defined, not declared, and teq.dfy splits
  into definitions and derived lemmas.
- Traces work as a data type (teq-def.dfy). Should sequences get a data
  type as well, or stay those of SMT-LIB with the views `[]` and
  `ys + [y]`?
- Should teq.dfy declare `Trace` as this data type, with the unfolding
  lemmas for proofs only, or should the definitions stay in a separate file
  for proofs?
- Should derived lemmas be generated at build time into a file, like
  teq.dfy, or on demand per program?
