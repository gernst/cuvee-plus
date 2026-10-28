# Generator of the ACSL annotations of benchmarks/acsl

The annotations of the tasks in benchmarks/acsl are generated from tables, one per folder of sv-benchmarks; fixes of
an annotation go into its table, so that a regeneration keeps them.

- `annotate.py <folder> [files]` copies a task from the sv-benchmarks checkout (`SVB`, by default
  `~/Projects/sv-benchmarks/c`) when it is annotated already, and inserts the annotations of `specs/<folder>.py`
  (`SPECS`: per file, the loop annotations in textual order, function contracts, ghost text such as axiomatics and
  labels, a note for the header); the contracts of the harness are added automatically. `annotate.py --list
  <folder>` lists the loops as the generator sees them. `specs/templates.py` holds shared shapes of invariants.
- `show.sh <folder> <files>` prints the programs without the harness.
- `check.sh <folders>` runs Cuvée (`-vcgen -z3`, 10 s, two at a time) on the tasks of the folders and writes
  `results/<folder>.tsv` (status, expected verdict, file, output); `check1.sh <file>` checks one task. Both take the
  jar from `JAR` (by default the `cuvee.jar` of the repository) and the timeout in seconds from `TIMEOUT`; run them
  from benchmarks/acsl. `results/` is not tracked.

All paths are relative to this folder (`ACSL` in the specs, `ROOT` in annotate.py).
