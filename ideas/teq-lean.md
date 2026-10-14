# Proofs of the database in Lean: open points

The pipeline of the plan of Oct 13, 2026 is implemented (doc/teq.md, lean/README.md): the statements of the stable
modules (teq.dfy, aggregation, arithmetic, 72 lemmas then) are generated from them by `scripts/lean/generate.py`, the
proofs taken over from the former `resources/cuvee/teq.lean` (59 statements were already identical, 10 differed only by
the premises now in `lean/premises.txt`, `maps_identity`, `consts_choice` and the rule `integer_eq` were proved anew;
the auxiliary `integer_eq` of the former file is `integer_cast`, and its uses of `max` and `min` are those of Lean,
`Max.max` and `Min.min`, since the printer declares the functions `max` and `min` of aggregation.dfy).
`scripts/lean/check.sh` checks it all in about 20 s.

Open:

- **Premises as `requires`.** The nine index premises of `premises.txt` (reads and prefixes within the loop) could
  become `requires` of the lemmas, if `-prove` decides `integer(k) < integer(n)` in the contexts of the goals;
  measure each on `mill -i test` and the SV-COMP rows (`benchmarks/sv-comp/dafny/expected.csv`) that use it. The
  length premise of `sum_consts_prefix` stays, since the engine knows no lengths. For now the premises are only
  documented (decision of the user, Oct 13, 2026).
- **A test in `mill -i test`** that generates `Database.lean` in memory and compares it with the committed one, so
  that a change of a stable module fails the Scala tests on machines without Lean (`generate.py --check` does it
  now, but only when called); a Scala change.
- **The legacy theorems** in `Proofs.lean` (those of lemmas of `legacy/teq.dfy` no longer in the stable modules):
  move them into a frozen `Legacy.lean`, or drop them with the legacy database. Since Oct 13, 2026 search, sorted,
  arrays, counters and strides are in `MODULES` too (131 lemmas): the theorems of arrays and counters checked
  unchanged except `current_trace_bounded` (its guard premise moved to `premises.txt`), the forward facts of search
  lost their `↔ True`/`↔ False`, sorted and strides were proved anew.
- **The bisection**: the rule with `bisection_lo` and `bisection_hi` was inconsistent under the semantics of an
  update without a case (bugs.md, Fixed); since Oct 14, 2026 `bisection` is a total definition with `{:fold}`, and the
  bounds are invariants of its update (`current_trace_invariant`, `cut_iff` of `Proofs.lean`).
- **The definitions of `cut` and the predicates of sorted.dfy** (in the modules since Oct 13, 2026, formerly models in
  `lean/TEQ/Definitions.lean`) fix one meaning of functions that the engines use through their lemmas only: `cut` on
  an empty interval and the partition points are chosen so (`lower` as the cut of `ar[j] < y`).
- **A Lean mode of the printer** (`Stmt` definitions and the preamble), replacing the text manipulation of
  `generate.py`; a Scala change.
- **Guards** (done in 0.46.11): `case g₁ => e₁ case g₂ => e₂` is printed as `if g₁ then e₁ else if g₂ then e₂ else
  unspecified`; the dead branches of complementary guards are dropped by `ite_lt_le` and its siblings, guards that are
  complementary on the values of a counter only by `trace_counter_congr`; overlapping guards still take the first
  case.
- The comments of `lean.Printer` still refer to `resources/cuvee/teq.lean` (Scala, left unchanged).
