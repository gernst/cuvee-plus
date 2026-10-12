# Progress of the ACSL annotations (Oct 11–12, 2026)

State of the work on `benchmarks/acsl`: what is done, how it was checked, the
obstacles met on the way, and what is open. [README.md](README.md) describes
the conventions of the annotations; the issues of Cuvée's ACSL support are
also in [TODO.md](../../TODO.md) (section "C frontend", item "ACSL on
SV-COMP"), where someone else picks them up.

## Done

- All 1198 tasks of the categories Arrays and Loops with the property
  `unreach-call` copied from `~/Projects/sv-benchmarks/c` (checkout of
  Dec 23, 2025) into `benchmarks/acsl/<folder>/`, with their `.yml` (reduced
  to the `unreach-call` property) and the licenses of the folders; the 225
  tasks of these folders with other properties only are not copied.
- All 1198 files annotated by hand, from spec tables per folder that a
  generator inserts (`pending/acsl/annotate.py`, `pending/acsl/specs/`, not
  part of the repository): harness contracts in every file, loop invariants
  and `loop assigns` in 1139 files, function contracts where the caller needs
  them, `axiomatic`s with logic functions and lemmas for sums and folds. The
  59 files without loop annotations are the 29 reducer outputs, the 10
  `*_abstracted` tasks without loops, the industrial programs of
  `loop-industry-pattern` (`aiob_*`, `ofuf_*`), and six programs with
  library calls, linked lists, or string functions (`loops/bubble_sort-2`,
  `n.c24`, `array-examples/relax-2-2`, `loops-crafted-1/discover_list`, ...).
- 1054 tasks have expected verdict `true`, 144 `false`. The false tasks get
  the invariants that hold and a header note saying why the assertion fails.
- Checked with Cuvée 0.38.0 (`-vcgen -z3`, 10 s per task, two in parallel,
  Oct 12, 00:00–01:30), results in `pending/acsl/results/*.tsv`; a second
  run with 0.39.3 (commit 0bebb8ae, unsigned ranges, `\at`, `\valid`, truth
  values of `&`) into `pending/acsl/results2/` was in progress when this file
  was written (three folders done).

## Results per folder with Cuvée 0.38.0

True tasks proved / true tasks; the cause of the rest in parentheses.

| folder | proved | of | causes of the rest |
|---|---|---|---|
| array-cav19 | 13 | 13 | |
| array-crafted | 9 | 43 | `axiomatic` (34, parse error) |
| array-examples | 55 | 61 | `\valid` (4), `__builtin_bswap32`, reducer |
| array-fpi | 68 | 68 | all 69 false tasks refuted |
| array-industry-pattern | 3 | 11 | structs (7), `\valid`, `\null` |
| array-lopstr16 | 1 | 11 | structs (9), `\valid` |
| array-multidimensional | 13 | 20 | unknown on unsigned sums (6, restated modulo 2^32 since), one refuted (same) |
| array-patterns | 4 | 30 | `axiomatic` (24), unknown (array26, parity of a count) |
| array-programs | 3 | 14 | `\min` (7), unknown on counts with integer division (4) |
| array-tiling | 27 | 27 | |
| loop-acceleration | 15 | 23 | unsigned ranges (7), `\at` (1) |
| loop-crafted | 3 | 6 | unsigned ranges (2), `\at` (1) |
| loop-industry-pattern | 0 | 17 | structs and pointers (16), reducers |
| loop-invariants(64) | 6 | 10 | unsigned ranges (3), bitwise `&` (1) |
| loop-invgen | 17 | 28 | reducers (10), goto into an else branch |
| loop-lit | 26 | 32 | reducers (6) |
| loop-new | 7 | 11 | reducers (3), unknown (`count_by_k`, nonlinear) |
| loop-simple | 6 | 6 | |
| loop-zilu | 26 | 27 | bitwise `&` on truth values (1) |
| loops | 27 | 37 | unsigned ranges (5), `\valid`, floats, structs, `&x`, pointers |
| loops-crafted-1 | 8 | 46 | unsigned ranges (38) |
| nla-digbench | 14 | 26 | shifts for powers of 2 and unsigned (5), unknown nonlinear (6), floats |
| nla-digbench-scaling | 127 | 280 | as nla-digbench; the unwindbound variants had a wrong counter bound (fixed since, see below) |
| reducercommutativity | 0 | 22 | `axiomatic` (22) |

With 0.39.3 so far: array-cav19 13/13, array-crafted 9/43, array-examples
56/61 (`\valid` accepted now, `data_structures_*` prove; `sanfoundry_43` and
`standard_strcmp` still fail, to be inspected).

## Obstacles met and how they were handled

- **Type ranges at loop heads.** Cuvée 0.38.0 quantified the loop state over
  all integers while the program wraps unsigned arithmetic, so every
  invariant over unsigned variables was refuted (most of
  `loops-crafted-1`). Reported in TODO.md; fixed in 0.39.3 for unsigned
  variables. The annotations were left as Frama-C/WP semantics demands (no
  explicit ranges).
- **Constructs beyond the support**: `\at(x, LoopEntry)`, `\valid`,
  `\valid_read` (fixed in 0.39.3), `\min`, `\null`, `axiomatic` with
  recursive logic functions, `lemma`s with labels, `(int *) array` to pass a
  matrix to a logic function. About 100 tasks (the reducer programs of
  `array-crafted` and `reducercommutativity`, `array-patterns`,
  `zero_sum*`, `loops/vogal-1`) depend on logic functions and give a generic
  parse error. The alternative, closed forms without logic functions, works
  where the array contents are deterministic (`array25–30`, `zero_sum_const*`,
  `array-fpi`, `array-programs`).
- **Bitwise operators** are uninterpreted; `&` of truth values in the
  `*_abstracted` tasks is handled in 0.39.3, `(x & 5) == 5` of
  `bin-suffix-5` is not provable with any invariant.
- **Nonlinear arithmetic**: Z3 answers unknown on the closed forms with
  products and integer division (`partial_mod_count_2-5`, `array26`,
  `geo*` modulo 2^64, `lcm2`, `prod4br`); cubic closed forms of
  `array27/29/30` are proved.
- **Diagnostics**: a refuted goal is one SMT-LIB string without the failing
  annotation; finding the culprit meant guessing (e.g. the global `n` of
  `eureka_05` that a contract must constrain, the counter of the unwindbound
  variants, see below).
- **Unwindbound variants** (`while (counter++ < N)`, a global counter shared
  by nested loops): a failed test leaves the counter at N+1, so the bound at
  a loop head is N plus the number of loop levels nested inside it; the
  first two attempts (`counter <= N`, `counter <= N+1` everywhere) were
  refuted. The spec computes the nesting depth now; `cohendiv-ll_unwindbound10`
  and `ps2-ll_unwindbound10` prove with 0.39.3, `egcd3-ll_unwindbound5`
  still does not (its base task proves).
- **Timeouts under load**: with the algorithm tests and the user's builds on
  the same four cores, trivial tasks hit the 10 s limit
  (`loop-lit/mine2017-ex4.*`, `loop-zilu/benchmark02`); alone they prove in
  2–3 s. All timeouts of the first run disappeared in the re-runs.
- **Semantics of the programs**: unsigned arithmetic required stating
  equalities modulo 2^32 or 2^64 (`nla-digbench/geo*`, `lcm*`,
  `array-multidimensional/*-u`), a function reading a global needs the
  global's value in its precondition (`eureka_05`), uninitialized
  variables (`c` in `break-1`, `MINVAL` in `pr*`) are arbitrary, and some
  `true` tasks are true only because of the specific values of
  uninitialized memory (`copy-partial-3-u`, `n.c40`); these are noted in
  the headers.
- **Mechanics**: the generator matches the number of loops per file
  (several specs were off by one and corrected); labels `L1:`, `L2:` had to
  be inserted as statements for `\at`; two `pkill -f` patterns matched the
  shell that issued them and killed the run; the module `nested.dfy` of the
  TEQ work had a pasted header that made `-include teq:nested` fail (fixed
  and committed as b423eeec).

## Open issues

1. Finish the run with 0.39.3 (`pending/acsl/results2/`), then update the
   table above and the numbers in TODO.md.
2. Tasks whose true verdict is not proved for reasons in the annotations
   rather than in the tool: `egcd3-ll_unwindbound*` (counter bound or
   invariants of the early exits), `nla-digbench/dijkstra-u`, `divbin2`,
   `hard-ll`, `hard2` (powers of two via shifts, `1 << k` is not interpreted),
   `lcm1` (modulo 2^32), `loop-invgen/nested6` (fixed, to be confirmed),
   `array-multidimensional/*-u` (restated modulo 2^32, to be confirmed).
3. Tasks that need tool support: logic functions and lemmas (about 100
   tasks), `\min` (7), `\null` (1), structs (30), floats (4), gotos of the
   reducers (29), `__builtin_bswap32` (1), `&x` and pointer comparisons
   (3).
4. False tasks: the annotations describe the loops but do not refute the
   assertion; Z3 refutes most of them anyway (`array-fpi` 69/69), many of
   the array ones end in unknown.
5. The annotations were never checked with Frama-C/WP; the `axiomatic`s
   (`fold`, `asum`, `msum`) and the lemmas `total`, `fold_swap`,
   `fold_rotate`, `asum_update` are stated, not proved.
6. `benchmarks/acsl` is not committed yet (the user decides); `pending/acsl`
   stays uncommitted like the rest of `pending/`.
