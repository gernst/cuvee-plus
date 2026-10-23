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

    ./Cuvee.sh -teq -include teq:aggregation -include teq:arithmetic \
      -include teq:arrays -include teq:counters -include teq:search \
      -include teq:sorted -include teq:strides -include teq:unsigned \
      -prove -split -prove -split -prove -fallback -z3 -timeout 900000 \
      -witness witness.yml [-arch 32|64] task

for a C program (`task.c`, `task.i`) or an SV-LIB script (`task.svlib`).
Without `-fallback -z3`, the goals that the lemma database does not close are
answered `unknown`. The answer is `correct` (the property holds), `incorrect`
(it is violated), or `unknown`, one for each `verify-call` of an SV-LIB script;
executions of a C program start in `main`. Errors, e.g. constructs that are not
supported, are reported as `(error ...)`. For a C program, `-witness` writes
the witness of the answer (format 2.0): for `correct` an invariant set without
invariants, for `incorrect` the call of `reach_error` as the target; nothing for
`unknown` and for SV-LIB. `-quiet` prints only the answers.
`./Cuvee.sh -version` prints the version.
