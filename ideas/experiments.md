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
| MonoCera (our run, 15 min) | 26 | 0 | 3 | 10 | 39 |
| MonoCera (paper) | 27 | 2 | 3 | 10 | 42 |
| Cuvée `-chc` (z3, Horn clauses) | 0 | 0 | 0 | 0 | 0 |
| TriCera, CPAchecker, SeaHorn (paper) | | | | | 0, 1, 0 |

- The direct comparison with a technique made for quantifiers and aggregates over arrays; no wrong results.
- Both 23, Cuvée only 56 (all 17 `sum`), MonoCera only 16: the strided and backward stores of `array-tiling`
  (`nr*`, `pnr*`, `pr*`, `rewnifrev*`), a weakness to discuss.
- Time: TEQ at most 20 s per proof, MonoCera up to 164 s.
- Horn clauses alone fail for lack of quantified invariants over arrays, which motivates the approach.
- Our MonoCera proves 3 fewer than the paper (`max/condn`, `max/sanfoundry_27_ground`,
  `forall/partial_lesser_bound-1`), probably the Java version (21 here).
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
| Cuvée `-teq -verify` (0.41.3, 60 s) | 133 true, 9 false | 125 true, 16 false |
| Cuvée `-teq` (0.36.3, 15 min) | 137 | 123 |
| Cuvée `-teq -fallback` (0.36.3, 15 min) | 147 | 277, 7 wrong |

- Arrays is where TEQ should stand out against the model checkers; on Loops over integers, the Horn-based and
  model-checking tools lead.
- The tasks have machine integers, which TEQ models in part (nondeterministic values in their ranges, unsigned
  wrap-around, since 0.36).
- `-fallback` had 7 wrong proofs (`fermat1-ll_unwindbound*`, see [TODO.md](../TODO.md)); with `-verify`, its
  goals are `:abstract`, which makes their refutations `unknown`, the wrong proofs remain to be checked.

## 3. Complementarity: TEQ and Horn clauses

TEQ and `-chc` together proved 151 Arrays and 307 Loops tasks on SV-COMP (15 min), far more than either: TEQ is
strong on arrays, Horn clauses on integer loops. The argument for TEQ as a complement to invariant inference,
and for a portfolio (see the TODO "Portfolio of TEQ and CHC").

## 4. Mathematical integers: the unbounded set

The 481 C programs of [benchmarks/sv-comp/c](../benchmarks/sv-comp/c) (all expected true), printed from the
Dafny translations of SV-COMP tasks, whose loop bounds are symbolic and whose arithmetic is unbounded.

| | proved (60 s) |
|---|--:|
| Cuvée `-teq -unbounded` | 228 |
| Korn `-u` (Oct 11, 2026) | 130 |
| either | 286 |

- TEQ 129 against 4 on the `array-*` folders, Korn ahead on `loop-lit`, `loop-invgen`, `nla-digbench`.
- Only Korn has a mode for mathematical integers; the other verifiers would be wrong by construction. A clean
  comparison with one Horn-based tool. Korn runs without fuzzing (`-random`), which executes the program on
  machine integers, and with `-confirm` (see `xml/korn.xml`).

## 5. Annotations against automation: the ACSL tasks

The 1161 tasks of SV-COMP Arrays and Loops annotated by hand with ACSL ([benchmarks/acsl](../benchmarks/acsl)):
`-vcgen -z3` with the given invariants proves 603 of the 838 true tasks, TEQ about 260 of the same programs
without annotations. How far TEQ gets automatically, and which tasks need annotations (nonlinear closed forms,
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

With Cuvée 0.41.3, `-verify`, 15 min, 2 cores, 7 GB, Intel Core i9-9900 (started Oct 12, 2026):

- running (started 11:31): `xml/cuvee.xml` and `xml/cuvee-fallback.xml` on SV-COMP Arrays and Loops and on the
  unbounded set (`-unbounded`), `xml/korn.xml` on the unbounded set (`-u`); at 11:5x, Cuvée had 437 of 440,
  728 of 764 and 468 of 481 results, Cuvée+Z3 332, 471 and 132, Korn 1 (it started last);
- to do: the MonoCera tests with `-unbounded` (`xml/cuvee.xml`, `xml/cuvee-fallback.xml`, `xml/cuvee-chc.xml`;
  the runs started without it were scrapped), MonoCera itself (`xml/monocera.xml`); SV-LIB `CTranslated` and
  `CoreVerification` (`xml/cuvee.xml`, `xml/cuvee-chc.xml`).

The other tools on SV-COMP come from the official SV-COMP 2026 results, MonoCera from our run and the paper.
