# The lemma database of -teq in Lean

The proofs of the lemmas of the stable modules of the database (`resources/cuvee/teq.dfy` and the modules
`aggregation`, `arithmetic`, `search`, `sorted`, `arrays`, `counters`, `strides`, `unsigned`, `series` of
`resources/cuvee/teq`, the
`MODULES` of `scripts/lean/generate.py`), in Lean 4 without Mathlib, as the
library `TEQ` of the Lake project at the root of the repository (`lakefile.toml`, `lean-toolchain`):

- `TEQ/Semantics.lean` (by hand): the datatype of traces and the combinators `trace`, `maps`, `invs`.
- `TEQ/Database.lean` (generated): the functions of the modules as printed by `-print lean`, and each lemma as the
  proposition `Stmt.<name>`, its printed statement with the premises of `premises.txt`.
- `TEQ/Naturals.lean` (by hand): in the namespace `TEQ.N`, the definitions by recursion on naturals (`counter`,
  `consts`, `earlier`, `prefix`, `indexof`, `cutFrom`, `pow`, and those built on them), the statements over them, and
  their proofs by induction.
- `TEQ/Proofs.lean` (by hand): the theorem `<name>` of each lemma, from the theorem `N.<name>` of Naturals.lean
  through one bridge per definition (the definition over integers is the one over naturals at `toNat`, e.g.
  `counter i c n = N.counter i c n.toNat`, since a count that is not positive is no step).
- `TEQ/Check.lean` (generated): `example : Stmt.<name> := @<name>` for each lemma (`<name>_rule` for a lemma named
  like a function).
- `TEQ/Counterexamples.lean` (by hand): the lemmas without their premises are false.
- `premises.txt`: the premises that the printer does not produce and the engine does not check, each with the
  reason why the contexts of -teq provide it.
- `open.txt`: the lemmas without a proof, which the generator removes from the modules before printing, each with
  the reason.

`mill -i test` checks that the generated files are those of the current modules (test/src/cuvee/test/Lean.scala, by
`generate.py --check` with the classpath of the tests). Check with `scripts/lean/check.sh`, which fails if the generated files are not those of the current modules
(`--regenerate` regenerates them), if the build fails, or on a `sorry`. Regenerate with `scripts/lean/generate.py`,
which prints the modules with a copy of `cuvee.jar`. A changed lemma then fails in `Check.lean` until its theorem in
`Proofs.lean` states and proves the new statement. Details in `doc/teq.md`.
