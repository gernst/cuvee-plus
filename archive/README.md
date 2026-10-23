# Cuvée for SV-COMP

Cuvée is a deductive verifier for C programs (property `unreach-call`) and
SV-LIB scripts (property `correct-tags`), which needs no loop invariants: it
summarizes each loop by a Trace Equation System, whose goals it closes by
rewriting with a database of lemmas, and passes the goals that remain to the
SMT solver Z3.

Source code and documentation: https://github.com/gernst/cuvee-plus

## Contents

- `Cuvee.sh`: the executable, which runs `cuvee.jar` with the `z3` of this
  folder.
- `cuvee.jar`: Cuvée with the Scala library and its dependencies.
- `z3`: Z3 4.16 for x86-64 Linux.
- `smoketest.sh` and `examples/`: runs Cuvée by trace equation systems with
  the lemma database, with and without the fallback to Z3, and by constrained
  Horn clauses, each on a safe and an unsafe C program and SV-LIB script
  (12 runs in parallel), exit code 0 if all answers are as expected.
- `LICENSE`: the license of Cuvée (Apache 2.0); `LICENSE.z3`,
  `LICENSE.scala`, `LICENSE.sourcecode`, `LICENSE.snakeyaml`: those of the
  included software.

## Usage

Requires Java 21 (e.g. the Ubuntu package `openjdk-21-jre-headless`).

    ./Cuvee.sh -svcomp -fallback -z3 -timeout 900000 [-arch 32|64] task

for a C program (`task.c`, `task.i`) or an SV-LIB script (`task.svlib`).
`-svcomp`, as the first argument, stands for the options of SV-COMP: trace
equation systems with all modules of the lemma database (`-teq -include
teq:<module>`), the deduction engine with two rounds of splitting (`-prove
-split -prove -split -prove`), and the witness (`-witness witness.yml`); the
other arguments follow. Without `-fallback -z3`, the goals that the lemma database does not close are
answered `unknown`. The answer is `correct` (the property holds), `incorrect`
(it is violated), or `unknown`, one for each `verify-call` of an SV-LIB script;
executions of a C program start in `main`. Errors, e.g. constructs that are not
supported, are reported as `(error ...)`. For a C program, `-witness` writes
the witness of the answer (format 2.0): for `correct` an invariant set without
invariants, for `incorrect` the call of `reach_error` as the target; nothing for
`unknown` and for SV-LIB. `-quiet` prints only the answers.
`./Cuvee.sh -version` prints the version.
