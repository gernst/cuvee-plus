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
- To measure a jar other than the checkout's, e.g. one with a module of the database under test, while the checkout's
  `cuvee.jar` holds uncommitted changes of others: `--tool-directory <dir>` with `Cuvee.sh`, `cuvee.jar` and `z3` in
  `<dir>`, a path relative to the checkout (e.g. the git-ignored `out/bench/tool`; a directory outside it, e.g. in
  `/tmp`, is not available to the workers, whose runs then fail with "Cannot execute"). A definition with options of
  its own, e.g. an additional `-include`, is a copy in `out/bench/` with paths relative to it (`../../sv-benchmarks`).
- **One call per `<tasks>`**, never several `-t` in one call: tasks of different sets with the same file name get
  each other's results. Start one call per set, in parallel if needed, in the background (they take minutes).
- `-T` overrides the time limit of the definition (`-T 60s` for runs during development), `--vcloudCPUModel` its
  CPU model (the `require` of the xml).
- Limits during development: the CPU `AMD Ryzen 7 PRO 5750G with Radeon Graphics` or
  `Intel Core i7-6700 @ 3.40 GHz` (the i7-10700 does not work), `-T 120s`, the core and memory of the definitions;
  the standard sets are Arrays, Loops and the four of MonoCera, with `cuvee.xml` and `cuvee-fallback.xml`; new runs
  with `--vcloudPriority` one of `IDLE`, `LOW`, `HIGH`, `URGENT` (there is no `NORMAL`). Results of different CPUs are
  not comparable in time.
- Check the first log files of a run for a missing jar (`Unable to access jarfile`) and crashes
  (`Exception in thread`, `OutOfMemoryError`).

## Definitions

| file | contents |
|---|---|
| `xml/cuvee.xml` | `-svcomp -rules`: `-teq` with all modules of the database, `-prove -split -prove -split -prove` (the second round splits the disjunctions that the rules introduce), the witness (`Cuvee.svcomp`, doc/options.md); 15 min, 1 core, 7 GB |
| `xml/cuvee-fallback.xml` | the same with `-fallback -z3 -timeout 900000`, Z3 for the goals that remain |
| `xml/cuvee-acsl.xml`, `cuvee-chc.xml` | `-vcgen -z3` on `benchmarks/acsl` (the categories Arrays and Loops as in sv-benchmarks, the true tasks annotated with ACSL; `-split` for the task set `C.unreach-call.Loops-split`), `-chc` |
| `xml/cuvee-native.xml` | `cuvee.xml` with the native executable (`make native`, `Cuvee-native.sh`), which starts without a JVM: `PYTHONPATH=xml ./benchmark xml/cuvee-native.xml ...` with the tool-info module `xml/toolinfo/cuvee_native.py`, which uploads `Cuvee-native.sh`, `cuvee.native` and `z3`; the binary needs glibc 2.34 and zlib on the workers |
| `xml/cuvee-portfolio.xml` | the portfolio (see "The portfolio" below): `portfolio.py` runs Korn's fuzzer (`fuzz/`, 30 s), `-fallback -z3` and `-chc` in parallel on the native executable and prints the output of the first definite answer; `PYTHONPATH=xml ./benchmark xml/cuvee-portfolio.xml ...` with the tool-info module `xml/toolinfo/cuvee_portfolio.py`, which uploads the script, `Cuvee-native.sh`, `cuvee.native`, `z3` and the harness; the fuzzer needs `gcc` with `-m32` on the workers |
| `xml/cpachecker.xml`, `uautomizer.xml`, `korn.xml`, `symbiotic.xml`, `aise.xml`, `monocera.xml` | the other verifiers |

The definitions of Cuvée pass `-witness witness.yml`, a witness of SV-COMP for each answer to a C program
(without invariants, or with the target only), which BenchExec keeps (`<resultfiles>**/witness.*</resultfiles>`, as for the other
verifiers) in `results/<benchmark>.<timestamp>.files/`.

Run definitions and tasks of `cuvee.xml`:

| run definition | tasks |
|---|---|
| `SV-COMP27_unreach-call` | `C.unreach-call.Arrays`, `C.unreach-call.Loops` (the categories ReachSafety-Arrays and -Loops of `sv-benchmarks`, the standard sets), and `C.unreach-call.ControlFlow`, `-ECA`, `-Sequentialized`, the other categories of ReachSafety in which Korn participates (not Recursive and XCSP) |
| `MonoCera_unreach-call` | `C.unreach-call.MonoCera-Forall`, `-Max`, `-Min`, `-Sum` |
| `SV-LIB_correct-tags` | `SV-LIB.correct-tags.CoreVerification`, `SV-LIB.correct-tags.CTranslated` |
| `RAPID_unreach-call` | `Boogie.unreach-call.RAPID` (the 33 RAPID benchmarks in Boogie, [benchmarks/rapid](../benchmarks/rapid), with `-entry main`; also in `cuvee-fallback.xml` and `cuvee-chc.xml`) |

## The portfolio

[portfolio.py](../portfolio.py) is a wrapper outside the tool, which Cuvée itself does not know: it runs several
methods in parallel on a task and answers with the first definite result, after which it stops the others, since the
methods solve different tasks; Cuvée stays one method per call. The methods are a list in the script (`METHODS`):

- **fuzz**, Korn's fuzzer, for C only: the task compiled with `gcc` (`-m32` for `-arch 32`) and the harness in
  [fuzz](../fuzz) (copied from Korn, [fuzz/README.md](../fuzz/README.md)), whose `__VERIFIER_nondet_*` draw small
  values around 0 and record them, and whose `reach_error` prints `unsat` with the trace; each run ends after one
  second, runs repeat until 30 s of CPU time. A violation is answered `false`; the fuzzer never answers `true`.
- **fallback**, `-svcomp -rules -fallback -z3 -timeout 900000`, for C and SV-LIB: the TEQ proof, then the goals that
  remain for z3.
- **chc**, `-chc -prove -z3 -timeout 900000`, for C and SV-LIB: Horn clauses for Spacer.

The options of the call are passed to every method of Cuvée (e.g. `-arch 32`, `-unbounded`, `-witness witness.yml`).
The methods of Cuvée run until they answer or the limit of the run ends them, sharing the CPU time of the run, which
SV-COMP limits for all processes together; each method runs in its own process group, which stops z3 and the
compiled task with it. The output is that of the method that answers, so the tool-info module reads it as Cuvée's
(`xml/toolinfo/cuvee_portfolio.py`, after `cuvee.py`); a line on stderr names the method. With `-witness`, each
method of Cuvée writes its own file (`witness.fallback.yml`, `witness.chc.yml`), and the one of the method that
answers is copied to the requested file. The methods of Cuvée use the native executable (`cuvee.native`,
`Cuvee-native.sh`) if it is next to the script, which starts without a JVM and uses less of the shared memory,
otherwise the jar; `portfolio.py -version` prints Cuvée's version. Two methods that ever disagree on a task are a
bug of one of them, which is investigated, never decided by majority. Open points are in TODO.md ("SV-COMP").

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
  files that meet their requirements. `experiments.py` also writes the quantile plots of SV-COMP with the legend below the plot
  (`quantile-<category>-bottom.pdf`), for slides.
