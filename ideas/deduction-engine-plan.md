# Implementing the deduction engine: the joint trace first, then the packages

Plan of Oct 12, 2026 for [deduction-engine.md](deduction-engine.md), against the code of version 0.42.4. The
representation comes first: a loop is one trace of its whole state, the *joint trace*, and the per-variable trace
equations of today are projections of it, split off on demand when a lemma needs one. The engine packages that
follow are independent of each other and of the joint trace where stated, each built and tested in isolation in
its own worktree. The re-entrance guard of [reentrance-guard.md](reentrance-guard.md) is done (0.42.3) and set the
rule for all of this: a change lands only with the trace that explains the failure it removes, and only after
the harness (package A) loses no proof.

## 1. The joint trace

### 1.1 Why first

Section 4 of [deduction-engine.md](deduction-engine.md) found that the hard cases are those where the
decomposition into one equation per variable is wrong by construction: mutually dependent variables whose
equations are individually meaningless, inner loops whose equations become fragments over incomparable
dependency lists that do not see each other's facts, and the bookkeeping of dependency lists (equal counters,
injective selection, unused dependencies, arity variants). Every one of these disappears if the loop is a single
fold over its state and the per-variable equations are derived from it rather than produced by symbolic
execution. The engine packages below (congruence closure, lookup, the pin) then work on a representation with
one dependency list per loop instead of repairing the consequences of many. That is why the representation is
not package I at the end but the foundation.

### 1.2 The representation

For a loop with modified variables `x̄ = x₁, ..., xₘ` and choices `z̄`, symbolic execution yields paths with
branch conditions `Bᵢ` and results `x̄ᵢ`. Today it emits `m` equations `Xⱼ == trace(xⱼ₀, for ⌊K⌋, ⌊Y⌋, ... do ...)`.
Instead:

```
K == counter(0, 1, n)
S == trace(tupleₘ(x̄₀), for ⌊K⌋, Z̄ do s, k, z̄ :: case B₁ => tupleₘ(x̄₁) ... case Bₚ => tupleₘ(x̄ₚ))   -- with xⱼ read as tupleₘ_j(s)
invs(for ⌊K⌋, ⌊S⌋, Z̄ check k, s, z̄ :: guard ∧ (B₁ ∨ ... ∨ Bₚ))
xⱼ == tupleₘ_j(current(S))                                                                    for each j
```

One trace, one dependency list, one iteration constraint, the tuples of the prelude (`Tuples`, selectors
`tupleₘ_j`) as the state. Choices stay sequences `Z̄`, or become components of the state as well (a choice is a
value per iteration like any other), which makes `⌊K⌋, ⌊S⌋` the only dependency list of a loop; the second
form is the target, the first the intermediate step.

**Inner loops** are values of the outer update, not constraints: the summary of an inner loop in a path of the
outer body is `s' == tupleₘ_i(current(S'(s)))` with `S'(s)` the inner joint trace as a term over the outer
state `s`, and its number of iterations `n'`, counter `K'` and the inner trace itself are *ghost components* of
the outer state, so that the inner iteration constraints and the exit are conjuncts of the outer constraint
over the same `s`. Nothing is distributed over different dependency lists any more, which is the fragments
problem solved by construction, and the inner trace is simplified as a unit in the context of the outer
iteration, where `s` is bound.

### 1.3 Splitting on demand: projections

The per-variable trace of component `j` is the projection `πⱼ(S)`, defined by one rule in `Simplify.trace`,
not by a lemma:

```
πⱼ(S) == trace(tupleₘ_j(s₀), for ⌊K⌋, ⌊S⌋, Z̄ do x, k, s, z̄ :: case B₁ => x₁ⱼ ... case Bₚ => xₚⱼ)   -- with tupleₘ_j(s) replaced by x
```

The other components are read from the history `⌊S⌋` through `s`; a component that reads none of them (a
counter, a sum of the input) loses the dependency `⌊S⌋` by the existing normalization (unused dependencies are
dropped), and is then exactly the trace that the lemma database matches today (`counter_def`, `sums_def`, ...).
The simplifier introduces projections on demand:

- `tupleₘ_j(current(S))` becomes `current(πⱼ(S))` and `tupleₘ_j(earlier(i, ⌊S⌋))` becomes `earlier(i, ⌊πⱼ(S)⌋)`,
  whenever the component is read, so that reads of the state meet the acceleration lemmas;
- the map `maps(for ⌊S⌋ yield s :: tupleₘ_j(s))`, which the matcher synthesizes for a variable dependency of a
  pattern, is `⌊πⱼ(S)⌋`, so that the per-variable forms `⌊Y⌋` of the lemmas appear and a concrete pattern
  dependency `⌊counter(i, c, n)⌋` matches `⌊πⱼ(S)⌋` through the context once `πⱼ(S) == counter(...)` is known;
- a projection whose trace is rewritten to a closed form (a counter, `sums`, `stores`) is recorded as the
  equation `Xⱼ == closed form` of the context, which is the per-variable equation of today, now derived.

So a layered loop (counter, index, array, sum) splits itself apart lemma by lemma, in the order the lemmas
apply, and a loop whose variables depend on each other stays joint, where the lemma for its shape is one lemma
on the fold over the pair with higher-order guards, which is what the summaries of merge, gnome sort and the
lower bound are today after all their tying.

### 1.4 What the lemma language needs

- **Accumulator patterns over tuples.** A lemma on a joint fold names the components:
  `trace(tuple2(l₀, h₀), for ks do (lo, hi), k :: tuple2(F(lo, hi), G(lo, hi)))`, i.e. a tuple pattern in the
  accumulator position, matched by destructuring, with the components as bound variables of the update. The
  parser of lemmas and `Rewrite.matches` for `Trace` get this; the printer prints it. Without it, the joint
  lemmas can still be written with `tupleₘ_j(s)` selectors, which is what the first examples do.
- **Projection-aware dependencies.** A pattern dependency that is a variable, `ys`, matched against `⌊S⌋`, binds
  `ys` to `⌊πⱼ(S)⌋` for the component `j` that the body reads at the corresponding bound variable (today's
  synthesis of `Maps`, specialized to projections); this is the mechanism of `Rewrite.instantiate` with
  projections in place of general maps.
- The database itself is unchanged: its lemmas are about per-variable traces and apply to the projections.

### 1.5 Steps and tests

| step | what | tests | size |
|---|---|---|---|
| S1 | `TEQ.loop` emits the joint trace behind `-teq-joint` (choices as sequences, inner loops as values with ghost components); the printers print tuples as today | the goals of the `-teq` examples compared by hand on five files: counter, nested_sum, merge, bubble_sort, first_duplicate | 3 days |
| S2 | the projection rule in `Simplify.trace` and the three on-demand rewrites of 1.3; equal-length typing of `⌊S⌋` | the single-loop examples of `examples/dafny/teq` and `examples/c/teq` close under `-teq-joint` as under `-teq` (the harness, goals compared) | 1 week |
| S3 | projection-aware dependencies in `Rewrite.instantiate`; the per-variable equations recorded as context equations | the SV-COMP translations sampled (68) under `-teq-joint` against main's `-teq` | 1 week |
| S4 | inner loops as values with ghost components; the fragments of today no longer produced | `invs_counter_equation`, `invs_fragments`, nested_sum, nested_mult, row_sums, transpose without the module `nested` | 1 week |
| S5 | accumulator patterns over tuples in the lemma language | merge, gnome sort, lower bound with one lemma on the pair; bubble and cocktail with the inner fold as one side condition | 1 week |
| S6 | `-fallback` lowers tuple traces (one function per component), `-print lean` prints them; `-teq-joint` becomes the default, the expected outputs are regenerated deliberately, `-teq-split` keeps the old form for comparison for one release | the full harness, the C benchmarks at 60 s | 1 week |

What it retires: the module `nested` as far as the fragment lemmas go, `results`, the chain lemmas of row sums,
the fragment side conditions of all summaries, `invs_current_counter_other`, the identification of equal
counters, and the "open trace variable" pattern for tying dependencies to traces.

Risks: the SV-COMP databases were recorded with the per-variable form, so until S6 the comparison is by the
number of goals, not by text; the Lean semantics of tuple traces is immediate, the fallback encoding is not
(functions of two indices for the inner ghost traces); and the matcher's cost on a single large update with
`p` cases and `m` components, where today each equation has only the cases that change its variable (the
simplifier merges cases with equal results per component after projection, which recovers that).

## 2. The engine packages

Independent of each other unless stated; A first. Those marked (joint) are easier after section 1 and should
wait for S3; the others can start now in parallel worktrees.

### A. The harness
Four regression sets from a private copy of the jar, one core, exit status read; a package lands only if it
loses no proof and no test takes twice its time. The scripts of the guard work (`run.sh`, `algos.sh`, `sample.sh`,
`compare.py`) move into `scripts/regression/`.

| set | what | time |
|---|---|---|
| `mill -i test` | the default suite (997 tests, 64 s); `CUVEE_PRINTING=1` after parser or printer changes | 2 min |
| the algorithms | `CUVEE_ALGORITHMS=1 mill -i test` | 5 min |
| the Dafny translations | every fourth row of `benchmarks/sv-comp/dafny/expected.csv` (68 tasks), all 651 before landing, compared with main's jar | 15 min / 2 h |
| the C benchmarks | `./benchmark xml/cuvee.xml -r SV-COMP27_unreach-call -t C.unreach-call.Arrays` and `Loops`, `-T 60s`, the jar installed in the checkout, against the latest 60 s run of main | 15 min |
| MonoCera | the 125 tests with `-unbounded` against the 79 of `summary.md` | 25 min |

### B. Canonical forms (`simplify/Canon.scala`, standalone)
Pure functions on `Expr`: canonical polynomials (`i - 1`, `i + (-1)`, `-1 + i` one term), canonical combinators
(equal dependencies merged, unused dropped except the counter, a fixed order with the counter first, bound
variables renamed by position), guards as sorted sets of literals. Tested alone for idempotence and α-variants.
150 lines, three days. Used by C, E, L and the hashing of G.

### C. Closed conditions looked up (`Rewrite.conditions`)
A closed instance that is an `invs`, an equation of lists or an atom is looked up among `ctx.known` modulo
`Canon` before it is decided. 30 lines plus unit tests from the 21st cocktail condition and the flags fact of
first_duplicate. Retires the fresh variables and identifying equations of six files. Needs B. Less needed
after S4, since the fragments that these conditions pick up no longer exist, but still right for conditions on
the iteration constraints.

### D. Matcher repairs (`Rewrite.instantiate`, `Rewrite.apply`)
Rule variables renamed apart from the goal's free variables (findings 9, 21). The alternatives over dependencies
for an unbound variable dependency (finding 1) are superseded by S3's projection-aware instantiation; do them
only if S3 slips. Two days.

### E. The pin in the matcher (`Rewrite.matches`, fallback case)
A unit test per failing literal pattern (the step `-1` through the context, the store index `i - 1`, a
disjunctive guard, `m + n`, a higher-order summand), then one mechanism: a pattern subterm over bound or
instantiated variables that fails to match is abstracted by a fresh higher-order variable with `p == e` as a
closed condition decided after the match. 40 lines. Retires the pins of merge, insertion sort, gnome sort,
cocktail and the stores-ahead-down restatement; opens recurrences on `a[k - 1]`. Needs B.

### F. Definitions at variables (`Rewrite.rewrite`)
A variable with a non-variable definition gets the rules tried on the definition when a rule's left-hand side
has its head symbol. Ten lines. Retires the whole-atom left-hand sides. Subsumed by G, cheap now.

### G. Congruence closure, standalone (`simplify/CC.scala`)
A persistent union-find over terms with congruence propagation as a `Theory`: `assume(Eq)`, `repr` (a
non-variable definition if the class has one, a literal if it has one, else the smallest term), `members`,
`implied(Eq)`. Built and tested alone on terms; then wired into `Context` in place of `Chains.replace` and
`Chains.chain` (`↑`, `var_`, `used`, `free`, `acyclic`, the one-point rule), measured by the harness before H.
300 lines new, 150 removed, two weeks. With the joint trace, the per-variable equations of 1.3 are exactly what
the classes hold, so G and S3 meet in the middle.

### H. Arithmetic over classes (`CC` with `Poly`)
Classes of integer terms carry the polynomial of their representative; linear equations solved as `Chains.solve`
does, recorded as merges, reaching function arguments through `repr`. Tests: is_sorted closes, `pr2` without
`half_even`, nested sums without `mul_eq_cancel`. One week. Needs G.

### J. Triggers and forward facts (joint)
Instantiation of an `invs` over `⌊counter(0, 1, n)⌋` at an index `j` with `0 <= j < integer(n)` when `a[j]` or
`earlier(j, xs)` is read; facts on named traces (`:facts` lemmas) assumed when the term occurs, memoized per
class; a trigger table. With the joint trace there is one constraint per loop to instantiate, which makes the
trigger table trivial. Retires the definitional atoms, the lsearch pair, the `above_iterations_def` interference,
the cut of bsearch. One week after S3 and G.

### K. Exit splitting (`Simplify.or`)
The negated exit of a loop, marked by `TEQ`, distributed over the other disjuncts when a rule on their atoms
needs a literal of it. Two days. Retires the two-implication postcondition of first_duplicate.

### L. E-graph (`egraph/`, standalone library)
Hash-consed nodes over `Canon`, classes with a union-find, rebuilding, e-matching with pattern variables bound
to classes, extraction by size, a node budget; tested alone on arithmetic and uninterpreted terms; then binders
as nested e-graphs per combinator body; integration last as `-saturate`. With the joint trace, a loop is one
combinator and one nested e-graph, which is the case e-graphs with binders handle best. Decides whether rule
order still costs proofs after C to H; if the harness shows none, L stays a library. Two weeks for the library.

### M. Diagnostics (`-probe`, budgets, timeouts)
`-probe <lemma>` reports the first failing side condition of a named rule with the facts it was matched
against and the part of a left-hand side that did not match; a separate step budget for conditions whose
exhaustion leaves the condition undecided; a timeout that reports the goal it was working on. One week.
Independent; most useful during S2 to S5.

## 3. Dependency graph and order

```
A harness
S1 joint trace ── S2 projections ── S3 projection-aware matching ── S4 inner loops as values ── S5 tuple patterns ── S6 default
                                   │                                  │
B canonical ──┬── C lookup          J triggers (after S3 and G)        │
              └── E the pin                                           │
D renaming, F definitions, K exit splitting, M diagnostics: independent, any time
G congruence closure ── H arithmetic over classes
L e-graph library: after B, integrated last
```

Order: A, then S1 and S2 as the main line, with B, D, F, G, K, M in parallel worktrees; C and E once B is in;
S3 to S6 on the main line, J after S3 and G, H after G; L last. Each step is one commit with its tests, docs
(`doc/teq.md`, `doc/simplifier.md`), the retired lemmas removed from the examples with their expected outputs
regenerated deliberately, and a version bump (second digit for S6 and the integration of G).
