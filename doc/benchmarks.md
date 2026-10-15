# Benchmarks

Cuvée and other verifiers run on the SV-COMP tasks and on the local benchmarks with BenchExec in the VerifierCloud.

## Running

```
./benchmark xml/<definition>.xml -r <rundefinition> -t <tasks> [-T 60s] [--vcloudCPUModel "<model>"]
```

- `./benchmark` calls `vcloud-benchmark.py` of the BenchExec fork in `~/Tools/benchexec`
  (`--no-container --vcloudMaster localhost`); the tool module `benchexec.tools.cuvee` runs `Cuvee.sh` with
  `cuvee.jar` and `z3` of the checkout, which are uploaded at the start: build and copy the jar before
  (`mill -i assembly; cp out/assembly.dest/out.jar cuvee.jar`), and do not rebuild it before the upload is done.
  The result header names the version of the jar (`-version`).
- **One call per `<tasks>`**, never several `-t` in one call: tasks of different sets with the same file name get
  each other's results. Start one call per set, in parallel if needed, in the background (they take minutes).
- `-T` overrides the time limit of the definition (`-T 60s` for runs during development), `--vcloudCPUModel` its
  CPU model (the `require` of the xml).
- Limits during development: the CPU `Intel Core i7-6700 @ 3.40 GHz` (the i7-10700 does not work), 1 or 2
  minutes, 2 cores, 7 GB (four runs fit on one CPU); small subsets rather than whole categories, unless asked.
- Check the first log files of a run for a missing jar (`Unable to access jarfile`) and crashes
  (`Exception in thread`, `OutOfMemoryError`).

## Definitions

| file | contents |
|---|---|
| `xml/cuvee.xml` | `-teq` with the migrated modules of the database (`-include teq:<module>`), `-prove -split -prove -rules -verify`; 15 min, 2 cores, 7 GB |
| `xml/cuvee-fallback.xml` | the same with `-fallback` and Z3 for the goals that remain |
| `xml/cuvee-sample.xml` | the options of `cuvee.xml` on samples of Arrays and Loops, 2 min, i7-6700 |
| `xml/cuvee-acsl.xml`, `cuvee-chc.xml` | `-vcgen` on the ACSL tasks of `benchmarks/acsl`, `-chc` |
| `xml/cpachecker.xml`, `uautomizer.xml`, `korn.xml`, `symbiotic.xml`, `aise.xml`, `monocera.xml` | the other verifiers |

The definitions of Cuvée pass `-witness witness.yml`, a witness of SV-COMP for each answer to a C program,
without content for now, which BenchExec keeps (`<resultfiles>**/witness.*</resultfiles>`, as for the other
verifiers) in `results/<benchmark>.<timestamp>.files/`.

Run definitions and tasks of `cuvee.xml`:

| run definition | tasks |
|---|---|
| `SV-COMP27_unreach-call` | `C.unreach-call.Arrays`, `C.unreach-call.Loops` (the categories ReachSafety-Arrays and -Loops of `sv-benchmarks`) |
| `local_unreach-call` | `C.unreach-call.Unbounded`, `Dafny.unreach-call.Unbounded` (benchmarks/sv-comp) |
| `MonoCera_unreach-call` | `C.unreach-call.MonoCera-Forall`, `-Max`, `-Min`, `-Sum` |
| `SV-LIB_correct-tags` | `SV-LIB.correct-tags.CoreVerification`, `SV-LIB.correct-tags.CTranslated` |

`xml/cuvee-sample.xml` has the run definition `sample_unreach-call` with the tasks `C.unreach-call.Arrays-sample`
and `C.unreach-call.Loops-sample`: every 9th task of Arrays.set and Loops.set
([benchmarks/sv-comp/samples](../benchmarks/sv-comp/samples), 49 and 51 tasks).

## Results

A run writes to `results/`:
- `<benchmark>.<timestamp>.results.<rundefinition>.<tasks>.txt`: the table of verdicts, CPU times, and the
  statistics (correct true and false, incorrect), read by `scripts/compare.py`;
- `....xml.bz2`: the same with the system information, read by the scripts of the paper;
- `<benchmark>.<timestamp>.logfiles.zip`: the output of each task, with the rules of `-rules`.

Scripts:
- `scripts/compare.py <baseline.txt> <new.txt>`: tasks lost and gained, flips, CPU time on the tasks that both
  solve; report correct results split into true and false.
- `scripts/missing.py <logfiles.zip> <tasks>`: the rules that a baseline applied to each task and that the current
  database lacks, e.g. after a migration of a module.
- `scripts/table.py`, `scatter.py`, `quantile.py`, `rules.py`, `experiments.py`: the tables, plots, and rule
  statistics of the papers (`ideas/experiments.md`, [SV-COMP.md](../SV-COMP.md)), from the most recent result
  files that meet their requirements.
