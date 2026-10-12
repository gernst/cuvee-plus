# Experiments for a paper comparing TEQ with other techniques

Plan of Oct 12, 2026, from the runs so far. The numbers below mix versions from 0.36.3 to 0.41.3 and limits of
60 s and 15 min; they show what to expect, the paper needs the reruns at the end, with one version, `-verify`, and
the same limits for all tools.

## 1. Aggregates over arrays: the MonoCera tests

The 125 SV-COMP tests of the CAV 2023 paper on MonoCera (Amilon et al.), one per operator `\forall`, `\max`,
`\min`, `\sum` (see [benchmarks/monocera/summary.md](../benchmarks/monocera/summary.md)), each tool on the
paper's conversion of the programs for it.

| | forall (93) | max (4) | min (11) | sum (17) | total |
|---|--:|--:|--:|--:|--:|
| Cuvée `-teq` | 53 | 2 | 7 | 17 | 79 |
| MonoCera (our run, 15 min) | 26 | 2 | 3 | 10 | 41 |
| MonoCera (paper) | 27 | 2 | 3 | 10 | 42 |
| Cuvée `-chc` (z3, Horn clauses) | 0 | 0 | 0 | 0 | 0 |
| TriCera, CPAchecker, SeaHorn (paper) | | | | | 0, 1, 0 |

- The direct comparison with a technique made for quantifiers and aggregates over arrays; no wrong results.
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

| | Arrays (440) | Loops (764) | score |
|---|--:|--:|--:|
| Cuvée (0.42.1, `-verify`, 15 min) | 138 true, 9 false | 126 true, 16 false | 553 |
| Cuvée+Z3 (0.42.2, `-verify`, 15 min) | 148 true, 51 false | 283 true, 28 false | 941 |
| Cuvée (CHC) (0.36.3, 15 min) | 8 true, 45 false | 149 true, 41 false | 400 |

Official SV-COMP 2026 scores on the same tasks: Symbiotic 1099, UAutomizer 941, Korn 882, CPAchecker 852
(AISE, which did not enter Arrays, 982 on Loops); see `scripts/out/experiments.pdf`.

- Arrays is where TEQ should stand out against the model checkers; on Loops over integers, the Horn-based and
  model-checking tools lead.
- The tasks have machine integers, which TEQ models in part (nondeterministic values in their ranges, unsigned
  wrap-around, since 0.36).
- No wrong results. Cuvée+Z3 scores as UAutomizer (941), ahead of Korn and CPAchecker, behind Symbiotic.
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

A virtual portfolio of TEQ and `-chc` (correct if either is, 15 min): 341 true and 105 false correct, score
787 with no wrong results, against 551 for TEQ and 400 for CHC alone (TEQ+Z3 and CHC: 458 true and 126 false,
score 786, with the wrong results of `-fallback`). TEQ is strong on arrays, Horn clauses on integer loops. The argument for TEQ as a complement to invariant inference,
and for a portfolio (see the TODO "Portfolio of TEQ and CHC").

## 4. Mathematical integers: the unbounded set

The 481 C programs of [benchmarks/sv-comp/c](../benchmarks/sv-comp/c) (all expected true), printed from the
Dafny translations of SV-COMP tasks, whose loop bounds are symbolic and whose arithmetic is unbounded.

| | proved (15 min) | wrong |
|---|--:|--:|
| Cuvée `-teq -unbounded` (0.41.4) | 234 | 0 |
| Cuvée+Z3 `-unbounded` (0.42.2) | 290 | 0 |
| Korn `-u` (Oct 11, 2026) | 175 | 0 |

- Cuvée+Z3 against 0.41.4: the three wrong refutations through `bitand` are proved now, as are
  `nla-digbench/fermat1-ll` and `sqrt1-ll` (an error before); `nla-digbench/lcm1` times out (99 s before),
  possibly a proof that relied on the overlapping exits (to check).
- Cuvée and Korn: 91 both, 143 Cuvée only, 84 Korn only. With 60 s: Cuvée 228, Korn 130; TEQ 129 against 4
  on the `array-*` folders, Korn ahead on `loop-lit`, `loop-invgen`, `nla-digbench`.
- Only Korn has a mode for mathematical integers; the other verifiers would be wrong by construction. A clean
  comparison with one Horn-based tool. Korn runs without fuzzing (`-random`), which executes the program on
  machine integers, and with `-confirm` (see `xml/korn.xml`).

## 5. Annotations against automation: the ACSL tasks

The 838 tasks of SV-COMP Arrays and Loops annotated by hand with ACSL ([benchmarks/acsl](../benchmarks/acsl)),
303 of Arrays and 535 of Loops, all expected true (the 323 tasks expected false were removed): `-vcgen -z3` with
the given invariants proves 603 of them (0.40.0, 60 s), TEQ without annotations 263 of the same programs (0.41.4,
15 min), 614 either. How far TEQ gets automatically, and which tasks need annotations (nonlinear closed forms,
`\min`). The annotations are not checked with Frama-C.

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
| Cuvée `-teq` (0.39.0, 60 s, without `teq:nested`) | 125 | 2 | 0 |
| Cuvée `-chc` (0.39.0, 60 s) | 123 | 37 | 1 (a translation issue, since fixed) |

- TEQ proves, Horn clauses also refute: a portfolio as in 3.
- Other tools from the official results of an SV-LIB category, if SV-COMP has one; otherwise SV-LIB is a second
  frontend of Cuvée on the same programs, not a comparison.
- Rerun with `-verify` (`xml/cuvee.xml` and `xml/cuvee-chc.xml`, run definition `SV-LIB_correct-tags`, task sets
  `CTranslated` and `CoreVerification`), with `teq:nested` again.

## Ablations

- The modules of the lemma database: the default against `teq:nested`, `teq:sorting`, `teq:strides`.
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

To do: the MonoCera tests with `-unbounded` (`xml/cuvee.xml`, `xml/cuvee-fallback.xml`, `xml/cuvee-chc.xml`),
MonoCera itself (`xml/monocera.xml`); SV-LIB `CTranslated` and `CoreVerification` (`xml/cuvee.xml`,
`xml/cuvee-chc.xml`); `-chc` on SV-COMP with `-verify`; the ACSL tasks with `-verify` after the revised
annotations.

`scripts/experiments.py` makes `scripts/out/experiments.pdf` from the newest results that meet each experiment's
requirements (options, time limit), with blanks for the missing ones. The other tools on SV-COMP come from the
official SV-COMP 2026 results, MonoCera from our run and the paper.
