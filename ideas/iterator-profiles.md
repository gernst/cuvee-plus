# Iterator profiles and trace equation systems

The loop patterns of Nishimura, Lozi, Lawall, "Generating Loop Invariants for Deductive Verification using
Iterator Profiles" (ASE 2026, [doi:10.1145/3832783.3837530](https://doi.org/10.1145/3832783.3837530)), read
against TEQs: which ones a TEQ represents and the database can reason about, and which ones are hard. The
paper's benchmarks are in [benchmarks/loopannotator](../benchmarks/loopannotator); nothing has been run with
Cuvée yet (Oct 13, 2026).

## The approach in one paragraph

A user writes an *iterator profile* for each loop-header pattern: a Coccinelle pattern (matched before macro
expansion, e.g. `for_each_cpu(cpu, e) S`) plus ACSL templates. Symbolic execution of the body gives a summary
(C, T): C is the paths that continue, as (path condition, state); T is the path conditions of `break` and
`return`. Instantiating the templates gives three kinds of invariants:

- **I-I**: the range of the index.
- **I-E**: the exact value of each updated variable. A variable updated in many iterations gets a fresh recursive
  logic function per loop, with `{body}` for an iteration that runs the body and `{unvisited}` for one that skips
  it. A write `a[i]` gets a quantified invariant over the visited and the unvisited indices.
- **I-P**: for every index visited so far, no condition in T held.

Frama-C/WP checks the result. The lemmas that link the iterator to the logic function (the `.lemma` templates of
the cpumask profiles) are generated per loop and assumed. The paper's scope is *iterator-based* loops: the body
modifies neither the index nor what its next value depends on. It excludes nested loops, reads such as `a[i-1]`
from earlier iterations, pointer aliasing, and calls whose contracts do not give the result exactly.

## Correspondence

| LoopAnnotator | TEQ |
|---|---|
| summary C of the body (paths, states) | the guarded update `if B₁ then e₁, …` from symbolic execution |
| T (`break`/`return` paths) | guards that need not cover every case (Cuvée's deviation from the paper) |
| I-P invariant | the iteration constraint `all(for ⌊K⌋, … check …)`; `invs` facts |
| I-E with a recursive logic function | `current(trace(init, for ⌊K⌋, … do x, k ↦ update))`, one term for all loops |
| I-E as a quantifier over `a[qi]` | `stores` / `current_trace_conditional_store`, `selects` |
| I-I from the profile | the index trace, named `counter(i, c, n)` by an introduction rule; the bounds from `invs_counter_*` |
| iterator profile (per header pattern) | a database module per iteration concept, matched on combinators, not on syntax |
| `.lemma` templates, assumed per loop | acceleration lemmas, proved once (Lean) and matched |
| `{unvisited}` (an iteration that skips the body) | a case of the update that keeps the value: `case ¬P(k) ⇒ x` |
| `det_int(i)` in place of `nondet_int()` | fresh sequences `Z` as dependencies; no change to the program needed |

A TEQ is the exact description that their requirement R2 asks for, and it is generated for every loop, without a
profile (relatively complete, thm 4.7). Their profiles do two things: they name the index iteration, and they
choose a form of invariant that Frama-C can check. In TEQs both are the database's job.

## Iteration patterns (the profiles)

### Representable, and the database covers them today

- **Counting up**: `for (…; i < e; i++)`, `i <= e`, `++i`, `i = i + 1`, `i += c`, `while (i < e) { S; i += 2; }`
  (the Frama-C profiles `whilep1`, `whilep1x`, `whilep2`, `simpl01x`). The index is `counter(i₀, c, n)`, and the
  exit gives `steps` through `invs_counter_*`. Where in the body the index is updated does not matter: symbolic
  execution sees the whole body. Strides other than 1 in reads go to `strides`.
- **Counting down**: `while (i > 0) { i = i - 1; S }` (`whilem0`–`whilem2`), `for (i = n - 1; i >= 0; i--)`: a
  counter with step -1, `indexof_counter_down`.
- **Several loops in sequence** (most VAJRA tasks, `copy9` with ten copies): compositional. Each loop's TEQ refers
  to the previous one's `current(A)`, and `selects_stores` chains through them.

### Representable, the reasoning needs new lemmas

- **`for_each_cpu(cpu, mask)`**: the index is updated by `find_next_bit`, whose contract has two behaviors: the
  next set bit at or after the offset, or `size` if there is none. In a TEQ the index is a trace whose update is a
  fresh `Z` constrained by the contract in the iteration constraint: `cpu' = z`, `bits[z]`, and no set bit in
  `[cpu + 1, z)`. The concept that the database lacks is the **enumeration of a set by an increasing index**, which
  calls for a *reindexing lemma*: a trace over `⌊CPU⌋`, where `CPU` enumerates `{j | P(j)}` in increasing order,
  equals a trace over `⌊counter(0, 1, m)⌋` with the update guarded by `P(k)` and the value kept otherwise. After
  that, the existing lemmas (`stores`, sums, `invs`) apply unchanged. The paper's two hand-proved lemmas
  (`c_loopinv`, `c_loopinv2`, example 2) are the step and the gap of exactly this argument. Difficulty: the side
  condition of the reindexing lemma is an iteration constraint with a nested quantifier ("no set bit in between").
  The matcher must find it among the facts modulo renaming, as `Rewrite.known` does for closed `invs` conditions.
- **`for_each_cpu_and`, `for_each_cpu_andnot`, `for_each_set_bit`**: the same lemma with `P(j) = a[j] ∧ b[j]`,
  `a[j] ∧ ¬b[j]`, …. With `P` as a function variable, as `C`, `V` and `D` are in today's lemmas, one lemma covers
  what takes them three profiles.
- **`for_each_cpu_wrap(cpu, mask, start)`**: an enumeration of `{j ≥ start | P(j)}` followed by `{j < start |
  P(j)}`. The index is not monotone; it has two phases. The reindexing then yields a concatenation of two
  counters, `counter(start, 1, N - start)` and then `counter(0, 1, start)`, which needs lemmas that split sums,
  `stores` and `invs` over a concatenation of dependencies. `current_trace_two_phases` exists only for scalar
  updates. Their profile writes four quantified invariants, one per segment (Fig. 3c); a TEQ has one `all`, and
  the four cases appear only when it is accelerated.
- **Halving**: `while (n > 0) { …; n = n / 2; }` (`whilediv0`, `sum_digits` with `n /= 10`, `loops/4.c`, three of
  their failures). The trace of `n` is geometric with division. Its number of steps is a logarithm, which has no
  term in the database. Lemmas over `pow` exist for multiplication (`current_trace_geometric`); the inverse
  direction (steps bounded by `log_c(n₀) + 1`, or `pow(c, steps) ≤ n₀`) is missing.

### Hard

- **Linked lists**: `for (p = head; p; p = p->next)` (Linux-Simple: 33 traversals are failures in their
  evaluation). A trace of pointers with the update `next[p]` over a heap that the loop does not modify is
  representable once the heap is a map. Reasoning about it needs list segments and acyclicity, a concept that the
  database does not have. Cuvée's C frontend also does not support structs, so this is out of reach before any
  reasoning.
- **Search through pointers into the list**: `for (;;) { action = *action_ptr; … action_ptr = &action->next; }`
  (Linux-Simple 178). Pointers to pointers and aliasing.
- **Iterators over data structures with side effects in the body** (list insertion; FEC: 133 failures are calls
  whose contracts do not give the result exactly): a TEQ represents such a call by a fresh `Z` constrained by the
  contract. That is *more* than LoopAnnotator can do, which fails on these calls. But what follows are
  *partial descriptions* (bounds, frame conditions), the known weakness (see
  [../doc/prove.md](../doc/prove.md), forward lemmas in `-prove`), and a heap model.

## Body patterns

### Covered, or close

- **Conditional writes at the index**: `if (c(a[i])) a[i] = v;` (example 1 of the paper; VAJRA `cond*`, `mod*`,
  `res*`). `current_trace_conditional_store`. The guard reads `a[i]` in the current state, which at iteration `i`
  still holds `a₀[i]` (`stores_def_read_unmodified`).
- **Accumulators**: `sum += a[i]`, `count++` under a condition (example 2; `array_sum`, `sum_even`,
  `occurences_of_x`). `sums`, `counts`, `current_sums`. A conditional increment `case C ⇒ x + f(k), case ¬C ⇒ x`
  needs the two cases merged into `x + (if C then f(k) else 0)` before `sums` applies. That is the same merge as
  [conditional-stores.md](conditional-stores.md), for sums. Calls that the contract gives exactly
  (`get_load(...)` = a logic function) are plain terms in the update; the result stays symbolic,
  `x₀ + sum(map(… ↦ if online(k) then load(k) else 0))`.
- **Early exit**: `if (c) break;` / `return` (example 3; `search`, `array_find`, `equal_arrays`, most of the FEC
  successes). The iteration constraint over the guards that did not exit, and `search.dfy` (`not_occurs_prefix`,
  `above_iterations`). `current_trace_flag` for a found flag.
- **Minimum and maximum** (VAJRA `min`, `max`, `array_max_advanced`): `maxs`, `mins`, `current_maxs_*`. Facts about
  the position of the maximum are partial descriptions.
- **Products**: `fact.c`, `power.c`, `mult.c`. `current_trace_geometric` for a constant factor, the triangle lemmas
  for `i * …`. The factorial has no closed form: the trace stays named, and a specification with a recursive logic
  function needs the bridge below.

### Hard

- **Reads from earlier iterations**, `a[i-1]` (VAJRA `eqn2`–`eqn5`, `ncomp`, `pcomp`, `sqm`; their future work).
  A TEQ represents them: the read at iteration `k` is a select of the earlier stores at `k - 1`, i.e. the value
  written in the previous iteration. The written values are then themselves a trace, a *chain*
  (chains are not yet in [doc/teq.md](../doc/teq.md)). In `eqn2`, `a[i] = a[i-1] + 4` and then `b[i] = b[i-1] + a[i-1]`
  give `b[i] = 2i² + 2i + 1`. That needs (1) matching an index-shifted read against the stores of the same loop
  (the open TODO on patterns with `k - 1`), (2) turning stores whose value depends on the previous one into a
  trace over the values, and (3) closed forms of polynomial recurrences (`triangle_*` covers degree 2 partly).
- **Nested loops** (`bubble_sort`, 13 + 9 Linux tasks): representable (thm 4.8, `nested`, `sorting`), but this is
  where the engine still has its problems ([../doc/prove.md](../doc/prove.md), the state traces).
- **The index modified in the body** (binary search; outside their class): `-teq-state` with forward lemmas
  (`examples/dafny/algorithms/bsearch.dfy`, formerly `examples/dafny/state/bsearch_bisect.dfy`).
- **Specifications with user-defined recursive logic functions** (`array_sum` in the original Frama-C Problems,
  `sumArr`): the goal speaks about `sumArr(a, n)`, the TEQ about a trace. A generic bridge would be an
  introduction rule *generated* from a recursive definition of the form `f(n) = if n == 0 then init else g(f(n -
  1), n - 1)`: `current(trace(init, for ⌊counter(0, 1, n)⌋ do x, k ↦ g(x, k))) == f(n)`, proved once by induction
  for this form. This is the inverse of what LoopAnnotator does (it writes such functions), and it would let TEQs
  meet specifications written in that style ([TODO.md](../TODO.md), Proofs of teq.dfy in Lean).

## Summary by dataset

These are estimates from reading the tasks, not runs.

- **VAJRA (42)**: the `spec` variants carry the assertions. 38 are SV-COMP tasks (`array-fpi`, `array-crafted`)
  that the TEQ evaluation already contains. New: `compare`, `copy9`, `max`, `min`. The ten that LoopAnnotator
  fails on are mostly `a[i-1]` (`eqn*`, `ncomp`, `pcomp`, `sqm`), the chain case above.
- **Frama-C Problems (28 + originals)**: simple counters, sums, searches, products. The originals in
  `frama-c-problems/original` have contracts, partly with logic functions (`sumArr`), so they are verification
  tasks once the incorrect ones are fixed (footnote 4 of the paper). Nearly all are within today's database. The
  exceptions: `binary_search` (state traces), `bubble_sort` (nested), `sum_digits` and `4.c` (division),
  `reverse_array` (a swap of `a[i]` and `a[j]` with one counter up and one down: two stores per iteration that
  read each other, the swap of the state-trace examples).
- **Linux-Simple (321)**: about 100 `for (i = 0; i < n; i++)` loops, with `break`/`return` searches over struct
  fields. With structs in the C frontend most of them would be counter + search + conditional stores. The tasks
  have no properties. A TEQ evaluation would need properties, or a different measure (below).
- **Linux-FEC (236)**: 177 `for_each_cpu`, 27 `for_each_cpu_and`, 8 `for_each_cpu_wrap` among the loops found.
  These need the reindexing lemma for enumerations, the comma operator in loop conditions, and structs. They are
  the most interesting set for the database: a single concept covers almost all of it.

## What to do with it

1. **A database module `enumerations`**: the reindexing lemma for an index whose contract-constrained update
   enumerates `{j | P(j)}` in increasing order, with `P` a function variable; the two-phase variant for `wrap`
   later. It needs a Dafny example that duplicates the declarations of `core.dfy` and models `find_next_bit` by a
   contract. Test it first on the three motivating examples, translated by hand to Dafny.
2. **The merge of guarded increments** into a conditional summand for `sums` (see conditional-stores.md).
3. **The bridge from recursive logic functions**: an introduction rule generated from a recursive definition of
   the standard form.
4. **A measure of description, not of verification**, for sets without properties (Linux): the fraction of loops
   whose TEQ simplifies to terms without unnamed `trace`/`all`, i.e. a closed form or a named fragment. This
   corresponds to their I-E/I-P success rate and is comparable with it.
5. **For the frontend**: structs (as one map per field), the comma operator in conditions, and the cpumask macros
   (expanded, or the header used as is).
6. **For the paper**: cite it as the closest recent work. It shares the diagnosis (an exact description of loops,
   independent of the postcondition, and evidence that people cannot write it) but stops at generating the
   description. The reasoning stays per loop, and the lemmas are assumed per loop.
