# SV-COMP tasks with ACSL annotations

The 1198 tasks of the SV-COMP categories ReachSafety-Arrays and
ReachSafety-Loops with the property `unreach-call` (the sets `Arrays.set` and
`Loops.set` of [sv-benchmarks](https://gitlab.com/sosy-lab/benchmarking/sv-benchmarks),
checkout of Dec 23, 2025), copied from `sv-benchmarks/c/<folder>` with their
task definitions and licenses, in the same folder layout, and annotated by hand
with ACSL (Oct 11–12, 2026). The task definitions keep only the `unreach-call`
property; tasks of the folders with other properties only (termination, memory
safety, overflows) are not copied. [properties/unreach-call.prp](properties/unreach-call.prp)
is the property file they refer to. The 37 tasks whose programs use structs
(`array-industry-pattern/array_of_struct_*`, most of `array-lopstr16`,
`loop-industry-pattern/aiob_*` and `ofuf_*`, `loops/bubble_sort-2`, `n.c24`,
the two `verisec_OpenSER` tasks, `loops-crafted-1/discover_list`, `net_reset`,
`array-examples/relax-2-2`) were removed on Oct 12, 2026, since Cuvée's C
frontend does not support structs: 1161 tasks remain, 422 of Arrays and 739
of Loops. The upstream change of the allocations (sv-benchmarks ada89e0473b,
Oct 9, 2026: unchecked `malloc` and `calloc` replaced by `safe_malloc` and
`safe_calloc`, defined in the tasks) is merged into the 166 files it touches,
with the annotations unchanged.

The annotations are a first approximation written by judgement, without a
verifier: they are meant to be the invariants and contracts that prove the
expected verdict `true`, in the semantics of Frama-C/WP (mathematical integers
in annotations, the C types of the program variables implicit, memory
predicates). They were not checked with Frama-C. Each file starts with
`// ACSL annotations added by hand (benchmarks/acsl/README.md)`, followed by a
note where the annotations need explanation.

## Conventions

- The harness: `reach_error` requires `\false`, so that every call to it
  must be proven unreachable; `__VERIFIER_assert(cond)` requires `cond != 0`;
  `abort`, `exit`, `__assert_fail` ensure `\false`, which makes
  `assume_abort_if_not` and `__VERIFIER_assume` assumptions (`ensures cond !=
  0`); `__VERIFIER_nondet_*` assign nothing. All of these are added
  mechanically.
- Every loop gets `loop invariant`s and a `loop assigns` clause (the latter
  in ACSL syntax as far as the arrays are concerned, `a[0..N-1]`, `a[i][0..n-1]`).
  Functions other than `main` get contracts when the proof of the caller
  needs them (`requires`, `assigns`, `ensures`). Memory clauses (`\valid`,
  `\valid_read`, `\separated`, `\null`, `reads`) are left out, since arrays
  are values in Cuvée's C (removed on Oct 12, 2026). Globals read by a function are constrained in its
  precondition (`requires n == 5`), since a contract does not see their
  initial values.
- Unsigned arithmetic that wraps around in the program is stated modulo its
  type (`sn == (2*x) % 4294967296`, `nla-digbench/geo*`, `lcm*`, `hard-u`,
  `dijkstra-u`, `knuth`); the bit patterns of the powers of 2 and 4 use a
  shift (`\exists integer k; 0 <= k <= 64 && p == 1 << k`).
- Sums and folds over arrays are logic functions in an `axiomatic`, defined
  recursively over the length, with the step backwards, `n > 0 ==> f(a, n)
  == f(a, n-1) + a[n-1]`, whose instances z3 finds (`asum`, `sqsum` in
  `array-patterns`; `rsum` of a row and `msum` of the first rows of a matrix,
  `int **a`; `sum` for the `zero_sum*` tasks of `array-crafted`; `cnt` in
  `loops/vogal-1`; `fold` for the reducer programs of `array-crafted` and
  `reducercommutativity`, with the lemmas `fold_swap` and `fold_rotate` over
  two arrays `x1`, `x2`, which state the invariance under the swap of the
  first two elements and under a rotation; the global `N` of
  `reducercommutativity/rangesum` is a parameter of its `fold`). The loops
  that rotate the array refer to its values by `\at(e, LoopEntry)`. Where a
  final bound follows from an element-wise property of the arrays, it is
  stated as a `lemma` in the axiomatic (`array-patterns`, `lemma total`;
  `asum_update` over two arrays). Lemmas are trusted by Cuvée (`:free`). Counts in `array-programs`
  are closed forms with integer division and `\min`.
- Tasks with expected verdict `false` get the invariants that do hold (often
  those of the `true` variant) and a note on why the assertion fails; the
  annotations do not claim to prove them.
- Not annotated beyond the harness: the 25 outputs of the reducers
  (`*-reducer.c`, unrolled control flow with gotos) and the `*_abstracted`
  tasks without loops.
  `loops/lu.cmp`, `ludcmp`, and the verisec tasks carry bounds only.

## Checking with Cuvée

Cuvée reads the annotations since 0.38.0 (`c: ACSL annotations available`),
with `./Cuvee.sh -vcgen -z3 <task>`: no output means that all goals hold, a
refuted goal is printed as `(error "goal does not hold" "Sat" ...)`. The
results on these tasks (10 s per task, Oct 12, 2026) and what they show
about the support are recorded in [TODO.md](../../TODO.md), section "C
frontend", item "ACSL on SV-COMP": the dominant gap is that the C type ranges
of the program variables are not assumed at loop heads, so that invariants
over unsigned variables are refuted; `\valid`, `\at`, `\min`, logic
functions, and lemmas are not supported; bitwise `&` is uninterpreted.
