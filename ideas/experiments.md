# Experiments for a paper comparing TEQ with other techniques

Plan of Oct 12, 2026, updated Oct 14 with the runs of 0.46 (15 min, `-verify`); older rows are kept for the
comparison. `scripts/out/experiments.pdf` takes the newest runs of 0.46 only.

## 1. Aggregates over arrays: the MonoCera tests

The 125 SV-COMP tests of the CAV 2023 paper on MonoCera (Amilon et al.), one per operator `\forall`, `\max`,
`\min`, `\sum` (see [benchmarks/monocera/summary.md](../benchmarks/monocera/summary.md)), each tool on the
paper's conversion of the programs for it.

| | forall (93) | max (4) | min (11) | sum (17) | total |
|---|--:|--:|--:|--:|--:|
| Cuvée (TEQ) | 53 | 2 | 7 | 17 | 79 |
| Cuvée+Z3 (TEQ, 0.46.9, `-unbounded`, 15 min, i7-6700) | 59 | 3 | 9 | 17 | 88 |
| MonoCera (our run, 15 min) | 26 | 2 | 3 | 10 | 41 |
| MonoCera (paper) | 27 | 2 | 3 | 10 | 42 |
| Cuvée (CHC) | 0 | 0 | 0 | 0 | 0 |
| TriCera, CPAchecker, SeaHorn (paper) | | | | | 0, 1, 0 |

- The direct comparison with a technique made for quantifiers and aggregates over arrays; no wrong results.
- Rerun with 0.46.9 (Oct 13, after the migration of the lemma database, `-unbounded`, 15 min, i7-6700): Cuvée
  unchanged at 79, Cuvée+Z3 88, no wrong results.
- Both 24, Cuvée only 55 (all 17 `sum`), MonoCera only 17: the strided and backward stores of `array-tiling`
  (`nr*`, `pnr*`, `pr*`, `rewnifrev*`), a weakness to discuss.
- Time: TEQ at most 20 s per proof, MonoCera up to 274 s.
- Horn clauses alone fail for lack of quantified invariants over arrays, which motivates the approach.
- Our MonoCera proves 1 fewer than the paper (`forall/partial_lesser_bound-1`), none more.
- **Semantics: mathematical integers.** The paper set up all tools "with equivalent configurations; for instance,
  to use the SMT-LIB theory of arrays to model C arrays, and a mathematical (as opposed to machine) semantics of
  integers" (Sect. 6, CPAchecker with k-induction for that reason). MonoCera is TriCera with its default
  `-arithMode:math`, which the artifact's options do not change: small programs confirm that nondeterministic and
  uninitialized `int`s are unbounded and that `x + 1` does not overflow (`-arithMode:ilp32` reverses all three).
  The numbers of Cuvée above are of its default C semantics (inputs in their ranges, unsigned wrap-around); the
  comparison uses `-unbounded`, now in the task sets `MonoCera-*` of `xml/cuvee*.xml`. On six tests, among them
  four that only MonoCera proves, `-unbounded` changes no answer (Cuvée 0.41.3, 90 s).

## 2. SV-COMP ReachSafety-Arrays and -Loops

The breadth comparison, against the official SV-COMP results of CPAchecker, UAutomizer, Symbiotic, AISE, Korn,
and others (imported from the SV-COMP statistics, not run by us).

| | Arrays (440) | Loops (764) |
|---|--:|--:|
| Cuvée (TEQ, 0.42.1, `-verify`, 15 min) | 138 true, 9 false | 126 true, 16 false |
| Cuvée (TEQ, 0.46.9, `-verify`, 15 min, i7-6700) | 138 true, 9 false | 149 true, 16 false |
| Cuvée+Z3 (TEQ, 0.46.9, `-verify`, 15 min, i7-6700) | 148 true, 48 false | 230 true, 20 false |
| Cuvée (CHC, 0.46.9, 15 min, i7-6700) | 8 true, 45 false | 150 true, 41 false |
| Cuvée+Z3 (TEQ, 0.42.2, `-verify`, 15 min) | 148 true, 51 false | 283 true, 28 false |
| Cuvée (CHC, 0.36.3, 15 min) | 8 true, 45 false | 149 true, 41 false |
| Cuvée (TEQ, 0.42.1, `-verify`, 60 s, i9-9900) | 130 true, 9 false | 125 true, 16 false |
| Cuvée (TEQ, 0.46.5, `-verify`, 60 s, i7-6700) | 136 true, 9 false | 145 true, 16 false |
| Cuvée (TEQ, 0.46.13, `-verify`, 60 s, i7-6700) | 144 true, 53 false | 148 true, 24 false |

The other tools: the confirmed results of SV-COMP 2026 on the same tasks, see `scripts/out/experiments.pdf`. No
scores, since Cuvée produces no witnesses: they are only meaningful with witness validation.

- 0.46.13 adds the case splits, the recurrences in arrays and the counterexamples without a solver: against
  0.46.8 at 60 s, 52 gained and none lost on Arrays (44 of them unsafe tasks refuted), 12 gained and 1 lost
  (ps2-ll_unwindbound1, a time out) on Loops.
- The 60 s rows compare the database migration (Oct 13, 0.46.x: one trace per strongly connected component,
  `-prove`, the migrated modules with `-include`, a second round of `-split -prove`) with the per-variable form
  (0.42.1, `-simplify`, the whole database and `teq:nested`); not in `scripts/out/experiments.pdf`, which takes the
  15 min runs. 0.46.5 loses 11 tasks of 0.42.1 (Arrays: indp5, revcpyswp2, time outs; Loops: in-de41 to in-de62,
  sum_by_3_abstracted, sum_array-2-2, while_infinite_loop_4) and gains 37; see doc/teq.md.
- Arrays is where TEQ should stand out against the model checkers; on Loops over integers, the Horn-based and
  model-checking tools lead.
- The tasks have machine integers, which TEQ models in part (nondeterministic values in their ranges, unsigned
  wrap-around, since 0.36).
- No wrong results.
- `-fallback` had 5 wrong proofs in 0.42.1, `nla-digbench-scaling/fermat1-ll_unwindbound{1,5,10,20,50}`
  (the other two of the 7 in 0.41.4 time out now): `TEQ` told the exits of an inner loop apart by assumptions
  only, an enclosing loop guards its cases by the branch conditions, such that the normal exit and the `break`
  exits overlapped, e.g. `case true => c case φ => c + 1`, and their lowering contradicted itself, from which z3
  proved any goal; the C loop `while (counter++ < k)` of the `*_unwindbound*` tasks is `while (true)` with a
  `break`. Fixed in 0.42.2 (exits by branch conditions, `examples/c/verify/teq_nested_break.c`;
  `fermat1-ll_unwindbound1` is `unknown`). The rerun with 0.42.2 lost no correct result to the fix (only
  `egcd2-ll_valuebound20` times out, 837 s before) and proves `fermat1-ll_valuebound50` and `_valuebound100` in
  addition; the `fermat1-ll_unwindbound*` tasks are `unknown` or time out.
- The wrong refutations of 0.41.4 are gone: `array-examples/sanfoundry_24-1` and `verifythis/lcp` were goals of
  helper functions out of the context of `main` (entry points, 0.42.0), the three on the unbounded set were
  refuted through an uninterpreted `bitand` on truth values (rules of the C prelude for 0 and 1; the
  other bit operations are `:abstract` since 0.42.1, their refutations `unknown`).

## 3. Complementarity: TEQ and Horn clauses

A virtual portfolio of TEQ and `-chc` (correct if either is, 15 min): with 0.46.9, 356 true and 106 false
correct, against 287 and 25 for TEQ and 158 and 86 for CHC alone; TEQ+Z3 and CHC 413 true and 119 false, all
without wrong results (0.42: 341 and 105, with the wrong results of `-fallback` then). TEQ is strong on arrays, Horn clauses on integer loops. The argument for TEQ as a complement to invariant inference,
and for a portfolio (see the TODO "Portfolio of TEQ and CHC").

## 4. Mathematical integers: the unbounded set

The 481 C programs of [benchmarks/sv-comp/c](../benchmarks/sv-comp/c) (all expected true), printed from the
Dafny translations of SV-COMP tasks, whose loop bounds are symbolic and whose arithmetic is unbounded.

| | proved (15 min) | wrong |
|---|--:|--:|
| Cuvée (TEQ, `-unbounded`, 0.41.4) | 234 | 0 |
| Cuvée+Z3 (TEQ, `-unbounded`, 0.42.2) | 290 | 0 |
| Korn `-u` (Oct 11, 2026) | 175 | 0 |
| Cuvée (TEQ, `-unbounded`, 0.46.13, i7-6700) | 263 | 0 |
| Cuvée+Z3 (TEQ, `-unbounded`, 0.46.13, i7-6700) | 299 | 0 |
| Cuvée (CHC, `-unbounded`, 0.46.13, i7-6700) | 144 | 0 |
| TriCera, MonoCera artifact, `-arithMode:math` (i9-9900) | 137 | 0 |

- Rerun on Oct 14, 2026 with 0.46.13 after the migration of the lemma database (15 min, i7-6700): Cuvée 234 to
  263, Cuvée+Z3 290 to 299, and Horn clauses (`-chc -z3`, new in this table) 144, no wrong results; the Horn
  clauses prove fewer than Korn, also a Horn-based tool, and far fewer than TEQ.
- Cuvée+Z3 against 0.41.4: the three wrong refutations through `bitand` are proved now, as are
  `nla-digbench/fermat1-ll` and `sqrt1-ll` (an error before); `nla-digbench/lcm1` times out (99 s before),
  possibly a proof that relied on the overlapping exits (to check).
- Cuvée and Korn: 91 both, 143 Cuvée only, 84 Korn only. With 60 s: Cuvée 228, Korn 130; TEQ 129 against 4
  on the `array-*` folders, Korn ahead on `loop-lit`, `loop-invgen`, `nla-digbench`.
- TriCera (Oct 14, the TriCera of the MonoCera artifact, `xml/tricera.xml`, 15 min, i9-9900): 137 proved, no
  wrong result after the programs were made memory safe, which TriCera checks as well (benchmarks/sv-comp/c/README.md:
  arrays sized for their accesses, `0 < N` before the declarations, consecutive declarations as one, since this
  TriCera aliases separately declared arrays and answered 33 safe programs unsafe before); the result of
  standard_vararg_ground, fixed after the run, is patched in from a local run (a time out), the original result
  files are kept as `results/tricera.2026-10-14_07-59-30.*.orig`.
- Only Korn and TriCera have a mode for mathematical integers; the other verifiers would be wrong by construction. A clean
  comparison with one Horn-based tool. Korn runs without fuzzing (`-random`), which executes the program on
  machine integers, and with `-confirm` (see `xml/korn.xml`).

## 5. Annotations against automation: the ACSL tasks

The tasks of SV-COMP Arrays and Loops with ACSL ([benchmarks/acsl](../benchmarks/acsl)), since Oct 23, 2026 laid
out exactly as the C categories (1204 tasks, 875 true), of which the 838 true tasks of Arrays (303) and Loops (535)
that Cuvée's C supports have annotations, with the invariants as given: `-vcgen -split -z3` (`xml/cuvee-acsl.xml`).
The table below is of the earlier layout, the 838 annotated tasks only, `-split` for the Split set alone.

| | Arrays | Loops | Split | wrong |
|---|--:|--:|--:|--:|
| `-vcgen -z3` (0.40.0, 60 s) | | | | 603 proved in all |
| `-vcgen -z3 -verify` (0.46.13, 15 min, Xeon E3-1230 v5) | 285 | 423 | 45 | 2 false |

- TEQ without annotations proves 263 of the same programs (0.41.4, 15 min), 614 either (0.40.0); to be recomputed
  for 0.46.
- The two wrong answers, false on data_structures_set_multi_proc_ground-2 and
  data_structures_set_multi_proc_trivial_ground (expected true), came from arrays passed by value to a function that
  changes them; the tasks (and sanfoundry_43_ground) take their arrays as global variables since, and prove
  (locally, 0.46.14).
- The annotations are not checked with Frama-C.

## 6. SV-LIB: the verification tasks

Only the verification tasks: `SV-LIB.correct-tags.CTranslated` and `CoreVerification` (a handful of hand-written
SV-LIB programs); `CoreValidation`, whose tasks are for validators, is out of scope, as are the BTOR2
translations (bitvectors).

The 253 tasks of `SV-LIB.correct-tags.CTranslated` (sv-benchmarks/sv-lib/c-translated, 189 expected true, 60
false): the loop folders of SV-COMP (`loop-zilu` 51, `loops-crafted-1` 56, `loop-acceleration` 40, `loops` 34,
`loop-lit` 26, and smaller ones), no arrays. SV-LIB has the integers of SMT-LIB, the arithmetic is mathematical
without an option. The same programs as in Loops in a second input language, with loop invariants and contracts
as tags (`correct-tags`).

| | true | false | wrong |
|---|--:|--:|--:|
| Cuvée (TEQ, 0.39.0, 60 s, without `teq:nested`) | 125 | 2 | 0 |
| Cuvée (CHC, 0.39.0, 60 s) | 123 | 37 | 1 (a translation issue, since fixed) |
| Cuvée (TEQ, 0.46.13, 15 min, Xeon E3-1230 v5, patched) | 140 | 29 | 0 |
| Cuvée (CHC, 0.46.13, 15 min, Xeon E3-1230 v5) | 129 | 40 | 0 |
| Cuvée+Z3 (TEQ, 0.46.14, 15 min, i7-10700, patched) | 142 | 29 | 0 |

- CoreVerification (Oct 14, 0.46.13): each configuration 1 correct true and 1 wrong true (loop-add.1, expected
  false), the other tasks `not supported` (the tag `upto` of the new conventions). The wrong true came from
  `verify-call` assuming the precondition of the callee; fixed in 0.46.14 (the precondition must follow from the
  declarations and axioms).
- The wrong true of `-teq` on CTranslated was loops-crafted-1/in-de20, expected false since sv-benchmarks
  c2d3abfeb, but the program satisfies its check for every integer `n` (inductive invariants checked with z3, see
  ideas/work-queue.md): the verdict is wrong, and our result files take it as true (patched, originals as
  `results/*.orig`); the official results of SV-COMP 2026 are unaffected (all three time out).
- loop-add.1 (CoreVerification): the wrong true of both configurations is fixed in 0.46.14 (`-teq` unknown, `-chc`
  correct false, confirmed locally); the result files of 0.46.13 are patched accordingly.
- TEQ proves more, Horn clauses refute more: a portfolio as in 3.
- The participants of the demonstration category SV-LIB of SV-COMP 2026 (official results, witnesses validated,
  in `scripts/official`): on CTranslated CPAchecker 111 true, 35 false (13 unconfirmed), PySvLib-CHC 118 true, 38
  false (11 unconfirmed, 1 wrong true, 1 wrong false), SvLibChecker 116 true, 36 false (7 unconfirmed); on
  CoreVerification CPAchecker 1 true, SvLibChecker 2 false. Each counted against the verdicts of its own run
  (SV-COMP 2026: 252 and 5 tasks; ours: 253 and 7). Cuvée (TEQ) proves the most, Cuvée (CHC) refutes the most.
- Cuvée+Z3 (TEQ) on SV-LIB (Oct 14, 0.46.14, Intel Core i7-10700, after the runs on the Xeon stalled): CTranslated
  142 true, 29 false (in-de20 patched as above), CoreVerification 1 true and loop-add.1 correct false, which
  confirms the check of the precondition at `verify-call` on the cloud. In total 143 true, 30 false, no wrong
  result: the most proofs of all tools on SV-LIB.

## Ablations

- The modules of the lemma database: teq.dfy alone against the optional modules (`aggregation`, `arithmetic`, `arrays`, `counters`, `search`, `sorted`, `strides`, `unsigned`), one at a time.
- The simplifier with and without `mods` and the remainders (version 0.36.2).
- The frequency of the rules (`scripts/rules.py`).
- Time to proof: most proofs take less than 20 s, the time limit barely matters.

## Reruns

Done (Oct 12, 2026, 12:47–13:55, Cuvée 0.41.4, `-verify`, 15 min, 2 cores, 7 GB, Intel Core i9-9900, complete
result files): `xml/cuvee.xml` and `xml/cuvee-fallback.xml` on SV-COMP Arrays and Loops and on the unbounded set
(`-unbounded`), `xml/korn.xml` on the unbounded set (`-u`). An earlier attempt at 11:31 lost the results still
running when the connection to the cloud master broke (11:54).

Done (Oct 12, 2026, 16:51–17:16, Cuvée 0.42.1, the same setup, complete): `xml/cuvee.xml` and
`xml/cuvee-fallback.xml` on SV-COMP Arrays and Loops (section 2). Before, the same with 60 s: no wrong results,
the `fermat1-ll` tasks time out at 60 s.

Done (Oct 12, 2026, 17:29–17:55, Cuvée 0.42.2, the same setup, complete): `xml/cuvee-fallback.xml` on SV-COMP
Arrays and Loops and on the unbounded set, after the fix of the exits of loops; no wrong results.

Done (Oct 13, 2026, from 22:11, Cuvée 0.46.9, 15 min, 2 cores, 7 GB, Intel Core i7-6700, after the migration of the
lemma database): `xml/cuvee.xml` on SV-COMP Arrays (138 true, 9 false) and Loops (149 true, 16 false),
`xml/cuvee-fallback.xml` on Arrays (148 true, 48 false) and Loops (230 true, 20 false), `xml/cuvee-chc.xml` on
Arrays (8 true, 45 false) and Loops (150 true, 41 false), the MonoCera tests with `xml/cuvee.xml` (79) and
`xml/cuvee-fallback.xml` (88), all without wrong results (`scripts/out/experiments.pdf` takes only these runs of
0.46; the unbounded set and SV-LIB are pending).

Done (Oct 13, 2026, 19:44–21:17, Cuvée 0.46.3 to 0.46.5, 60 s, 2 cores, 7 GB, Intel Core i7-6700, complete):
`xml/cuvee.xml` on SV-COMP Arrays and Loops after each step of the database migration (`-T 60s --vcloudCPUModel`,
see doc/benchmarks.md); correct results Arrays 105, 124, 140, 144, 145 and Loops 128, 148, 154, 154, 161, no wrong
results.

Done (Oct 14, 2026, Cuvée 0.46.13, 15 min, 2 cores, 7 GB): the unbounded set with `xml/cuvee.xml`,
`xml/cuvee-fallback.xml`, `xml/cuvee-chc.xml` (i7-6700) and `xml/tricera.xml` (i9-9900), section 4; the ACSL tasks
with `xml/cuvee-acsl.xml` and SV-LIB `CTranslated` and `CoreVerification` with `xml/cuvee.xml` and
`xml/cuvee-chc.xml` (Xeon E3-1230 v5), sections 5 and 6.

To do: SV-LIB `CoreVerification` with `-teq` and `-chc` on 0.46.14 (patched for now; the fallback run confirms
the fix);
the three changed ACSL tasks (or all, for one version); TEQ on the programs of the ACSL tasks with 0.46.

`scripts/experiments.py` makes `scripts/out/experiments.pdf` from the newest results that meet each experiment's
requirements (options, time limit), with blanks for the missing ones. The other tools on SV-COMP come from the
official SV-COMP 2026 results, MonoCera from our run and the paper.
