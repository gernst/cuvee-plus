# Cuvée for SV-COMP

Cuvée is a deductive verifier for C programs, which proves the property
`unreach-call` without loop invariants: it summarizes each loop by a trace
equation system, whose goals it closes by rewriting with a database of lemmas,
and passes the goals that remain to the SMT solver Z3.

Source code and documentation: https://github.com/gernst/cuvee-plus

## Contents

- `Cuvee.sh`: the executable, which runs `cuvee.jar` with the `z3` of this
  folder.
- `cuvee.jar`: Cuvée with the Scala library and its dependencies.
- `z3`: Z3 4.16 for x86-64 Linux.
- `smoketest.sh` and `examples/`: runs Cuvée on two safe and one unsafe
  example, exit code 0 if the results are as expected.
- `LICENSE`: the license of Cuvée (Apache 2.0); `LICENSE.z3`,
  `LICENSE.scala`, `LICENSE.sourcecode`, `LICENSE.snakeyaml`: those of the
  included software.

## Usage

Requires Java 21 (e.g. the Ubuntu package `openjdk-21-jre-headless`).

    ./Cuvee.sh -teq -simplify -split -simplify -fallback -z3 -timeout 900000 [-arch 32|64] task.c

No output means that the property holds. A goal that simplifies to false,
reported as `(goal false)` or `(error "goal does not hold" "Sat" "false")`,
means that it is violated; other goals that remain are not refuted, the
result is unknown. Cuvée does not produce witnesses. `./Cuvee.sh -version`
prints the version.
