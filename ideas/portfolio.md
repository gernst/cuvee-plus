# A portfolio of Cuvée's methods

A wrapper outside the tool, [portfolio.py](../portfolio.py), runs Cuvée's methods in parallel on a task and answers with the first definite result, after which it stops the others. The methods are
different, so their strengths add up; Cuvée itself
stays one method per call.

## Why

The engines solve different tasks. On SV-COMP (true/false), with `cuvee-fallback` at 120 s (0.52.3) and `-chc` from
the run of Oct 23, 2026 (15 min):

| Set | cuvee-fallback | -chc | -chc only | union |
|---|---|---|---|---|
| Arrays | 158/58 | 8/47 | 3/11 | 230 (+14) |
| Loops | 251/25 | 151/43 | 45/30 | 351 (+75) |
| SV-LIB CTranslated | 146/31 | 125/39 | 26/21 | 224 (+47) |

No answers conflict. `-fallback` already runs the TEQ proof first, so it subsumes `-teq -prove` (no task that only
the latter solves). Where Cuvée is weakest are the false tasks: Korn solves 151 false tasks of Loops that Cuvée does
not, 114 of them the `_unwindbound` variants of nla-digbench-scaling, by bounded exploration and fuzzing.

## Measured (Oct 26, 2026)

The portfolio on the cloud (120 s of CPU time for all methods together, one core, 7 GB, 0.52.4, native binary):

| Set | cuvee-fallback | portfolio | fuzz | fallback | -chc |
|---|---|---|---|---|---|
| Arrays | 160/62 | 158/89 | 0/86 | 153/1 | 5/2 |
| Loops | 252/29 | 289/146 | 0/135 | 147/0 | 142/11 |
| SV-LIB CTranslated | 146/31 | 173/52 | – | 55/13 | 118/39 |
| MonoCera-Forall | 64/0 (TEQ) | 70/0 | – | 70/0 | – |

(true/false; the last three columns are the methods whose answer won.) No wrong answer, checked against the expected
verdicts of the task definitions; the one mismatch is SV-LIB in-de20, whose expected verdict is wrong (bugs.md). The
fuzzer finds the false tasks that Cuvée misses (the `_unwindbound` variants, array-fpi), `-chc` the numeric ones; the
fallback loses a few true tasks of Arrays to the shared CPU time.

## The methods

What each is good at and where it fails, by the results so far:

1. **Fuzzing**, Korn's ([../korn](../../korn), `korn.tool.Fuzz`, `korn.tool.Confirm`): the C task compiled natively
   with `__VERIFIER.c` (every `__VERIFIER_nondet_*` through `__VERIFIER_next_nondet`) and a generator,
   `__VERIFIER_random.c` (small values around 0: 0, ±1, ±16, ±512, seeded by the clock) or `__VERIFIER_zero.c`; each
   run records its values and ends after one second (`alarm`), `reach_error` prints `unsat` with the trace and the
   seed; runs repeat until the timeout. `Confirm` replays a trace deterministically
   (`__VERIFIER_counterexample.c`) before `false` is answered, and the trace is the input of the violation witness.
   - Good at: shallow violations with few, small inputs (the `_unwindbound` tasks, array-fpi `*f`, loop-zilu).
   - Fails: deep or narrow conditions (`x == 123456`), large values; no `true` answers. Boundary values
     (`INT_MIN`, `INT_MAX`, the literals of the program) would be an extension of the generator.
   - C only, not SV-LIB or Boogie. Undefined behavior in a run could fake a violation: compile with
     `-fsanitize=undefined -fno-sanitize-recover` and discard such runs (to check what Korn does).
2. **cuvee-fallback** (`-svcomp -rules -fallback -z3`): the TEQ proof, then the remaining goals lowered for z3.
   - Good at: `true` with arrays and sums (Arrays 158 true, best of all verifiers), closed forms of loops.
   - Fails: `false` (only by evaluation of arithmetic goals), loops outside the database, nonlinear invariants
     that need inductive strengthening.
3. **-chc** (`-chc -prove -z3`, Horn clauses for Spacer).
   - Good at: numeric invariants without closed form, `false` by counterexamples of Spacer (Loops 43, SV-LIB 39).
   - Fails: arrays (Arrays 8 true), quantified invariants, nonlinear arithmetic.
4. **Bounded unrolling** (new, plan B of [prove-next.md](prove-next.md)): `-unroll k` with growing `k`, by `-vcgen`
   and z3.
   - Good at: `false` after a few iterations, and `true` with an unwinding assertion for loops with small literal
     bounds (reducercommutativity, `_unwindbound` true tasks).
   - Fails: unbounded loops (`true` never), deep violations.

## The wrapper

- A script in the archive next to the native binary (`cuvee.native`), called by the tool-info module instead of
  `Cuvee.sh`; it passes the task and the options to the methods, runs them in parallel, and prints the output of the
  first that is definite, which the tool-info module reads as usual. The methods are a data structure in the script
  (`METHODS`), to become a file of configurations.
- The methods of Cuvée run until they answer or the limit of the run ends them; the fuzzer has a timeout of CPU
  time (30 s), since it would otherwise draw until the end. SV-COMP limits the CPU time of all processes together
  (900 s), so the methods share it. Each method runs in its own process group, which ends z3 and the compiled task
  with it, the fuzzer with `RLIMIT_CPU` per run.
- The native binary removes the start of the JVM and its warming up per method and uses less memory, which matters
  for several methods sharing the memory limit.
- Answers: the first `true` or `false` wins, the other methods are killed. If two methods ever disagree on a task (in
  the measurements, where all run), that is a bug of one of them, investigated, never decided by majority.
- Witnesses: each method of Cuvée writes its own file (`witness.fallback.yml`, `witness.chc.yml` for `-witness
  witness.yml`), the one of the method that answers is copied to the file of `-witness`, since the methods run at the
  same time. The fuzzer writes none yet, so its `false` answers have no witness and would be unconfirmed in SV-COMP
  (221 on Arrays and Loops in the run of Oct 26, 2026); the cheapest fix is the trivial violation witness of
  `yml.Witness` (the target, the call of `reach_error`), the better one Korn's trace of the nondet values in order
  as the values of a `violation_sequence` (format in [witnesses.md](witnesses.md)).

## Steps

1. Measure each method alone on the same sets and limits, locally or on the cloud as the user permits (not `-chc` on
   the cloud), then compute the union and the timeout of the fuzzer.
2. Fuzzing: the replay of a trace (`Confirm`) before `false` counts; tests on the `_unwindbound` and array-fpi false
   tasks; Korn's harness is copied next to the script.
3. The wrapper on the native binary; the tool-info module and the benchmark definitions for it.
4. Bounded unrolling (plan B).
5. Violation witnesses of the fuzzer: first the trivial one, then with the values of its trace.
