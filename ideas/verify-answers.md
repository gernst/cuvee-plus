# Answers `correct`/`incorrect`/`unknown` with `-verify`

Proposal of Oct 12, 2026 (after 0.39.7 renamed the former `-verify` to `-vcgen`), implemented in 0.41.0 as
revised: `-z3` and `-cvc5` choose the solver, `-check` (the default) checks as before, `-verify` answers with the sink
[pipe/Verify.scala](../src/cuvee/pipe/Verify.scala), the answers are aggregated over all obligations so far, given to
each `verify-call` and to the end of an input without `verify-call`, and the `check-sat` of `-chc` states its
expected status by `(set-info :status sat)` (see [doc/architecture.md](../doc/architecture.md)).

## Problem

The verdict of a task is reconstructed by [cuvee.py](../cuvee.py) from output that differs by mode: no output,
remaining `(goal ...)` lines, errors of z3 (`"goal does not hold" "Sat"`), or `sat`/`unsat` of the Horn solver on
stderr. Whether a refuted goal is a counterexample depends on how the goal was produced, which cuvee.py can only
guess from the command line. This has led to wrong or inconsistent verdicts:

- `-vcgen -z3` on SV-LIB verification tasks, which have no loop invariants, refutes safe tasks (`loop-add`);
- z3's `Sat` after `-teq -fallback` is a violation for SV-LIB but unknown for C.

## Principle

`-verify` checks the program against the user's specification. Its answer is about the input as specified,
including what its contracts, loop invariants and options say. Hence procedure contracts and loop invariants are
specification, also in C with ACSL and the property unreach-call: a loop invariant that is too weak to prove the
assertions makes the task `incorrect`, even if `reach_error` is unreachable. `-unbounded` does not weaken an
answer either: it changes the meaning of the task, it is no approximation.

## Flag and output

- `-verify` changes only the output. The pipeline is always given explicitly (`-vcgen -z3`,
  `-teq -simplify ...`, `-chc -z3`); there is no default, and `-verify` without a transform is an error.
- stdout carries one answer per unit: `correct`, `incorrect` or `unknown`, as SV-LIB answers `verify-call`. The
  unit is each `verify-call` in SV-LIB (its goals reach the sink before the command) and the whole input
  otherwise (C, Dafny, Boogie, SMT-LIB), answered at the end. Nothing else goes to stdout.
- stderr carries the diagnostics: the refuted goal, or why a refutation only counts as `unknown`.
- Errors stay as now, with the message and a non-zero exit code, and no answer for that unit.
- `-print` and `-o` are rejected together with `-verify`.

## The answering sink

A sink at the end of the pipeline:

- with a solver, it uses the solver's answer for each goal; for `-chc`, the answer to `check-sat` on the clauses;
- without a solver (`-teq -simplify`), it reads the goals that reach it: `true` has been dropped already, `false`
  is refuted, every other goal is open.

It answers `incorrect` if a goal that is not `:abstract` is refuted or the clauses are `unsat`, `correct` if every
goal is proved or the clauses are `sat`, and `unknown` otherwise.

## Which refutations are real

Only actual approximations make a refutation `unknown`; the goal attribute `:abstract` marks them:

| Source | Refutation means |
|---|---|
| procedure contracts: `ensures`, preconditions of calls, contracts as summaries of calls | `incorrect`, they are the specification |
| loop invariants given by the user (SV-LIB tags, Dafny/Boogie `invariant`, ACSL `loop invariant`) | `incorrect`, they are specification, also when too weak |
| loops without an invariant under `-vcgen` (implicitly `true`) | `unknown`: `VCGen` marks the goals behind such a loop `:abstract` |
| goals of `-fallback`, whose encoding generalizes | `unknown`: `Fallback` marks all its goals |
| `TEQ` and `Horn` | `incorrect`, their steps are exact with respect to the given contracts |
| `-unbounded` | no effect |

## cuvee.py and the benchmark definitions

- The definitions in `xml/` add `-verify`.
- `determine_result` reads the answers: any `incorrect` is false (`RESULT_FALSE_REACH` for unreach-call,
  `RESULT_FALSE_PROP` for correct-tags), at least one answer and all `correct` is true, otherwise unknown; no
  answer is an error.
- The parsing per mode, including the special cases of `-chc` and `-unbounded`, is removed.

## Tests

Per mode, a safe and an unsafe example with `-verify`, and two that answer `unknown`: a loop without an
invariant under `-vcgen`, and a refutation after `-fallback`. Existing examples do not use `-verify`, their
output is unchanged.

## Implementation (0.41.0, worktree `verify`) and its problems

### What was built

- `Status` has the further cases `Correct` and `Incorrect`, which with `Unknown` are the answers, printed by all
  printers.
- `-z3` and `-cvc5` choose the solver; `-check`, the default with a solver, checks as before (a goal that does not
  hold is an error, `check-sat` and `get-model` are answered); `-verify` builds the sink
  [pipe/Verify.scala](../src/cuvee/pipe/Verify.scala). `Config.receiver` builds the sink from the final
  configuration, `Config.validate` rejects `-check` without solver, `-check` with `-verify`, `-verify` without
  `-vcgen`, `-teq`, or `-chc`, and `-verify` with `-print` or `-o`.
- The sink checks each obligation against its expected status (goals and lemmas: their negation `unsat`;
  `check-sat`: the `(set-info :status ...)` before it), aggregates the outcomes over the whole run, and answers each
  `verify-call`, and `Done` if there was no `verify-call`. The commands go to the solver directly. `Pipe`, `Stage`,
  `Sink` and the passive sinks are unchanged.
- `Horn` writes `(set-info :status sat)` before its `check-sat`, `VCGen` marks the goal of a procedure `:abstract`
  if one of its loops has no invariant, `Fallback` the goals it lowers.
- `cuvee.py` reads only the answers under `-verify`; the definitions in `xml/` pass `-verify`.
- Examples in `examples/{c,svlib,smtlib}/verify`, a unit test of the options and of the classification; 39
  expected outputs regenerated for the `set-info` line of `-chc` and `:abstract` of `-fallback`.

### Problems

1. **The modes disagree on a loop invariant that holds but is too weak.** In
   `examples/svlib/vcgen/invalid_invariant.svlib` (and `examples/c/verify/vcgen_weak_invariant.c`), `-vcgen`
   answers `incorrect`, since the invariant is the only summary of the loop, but `-chc` and `-teq` answer
   `correct`: `Horn` checks the invariant as a property of the loop head and infers its own invariant for the
   postcondition, `TEQ` summarizes the loop by its trace and checks the invariant along it. The decision "too weak
   invariants are incorrect" is therefore implemented by `-vcgen` only; for the property correct-tags of SV-LIB
   ("all annotations hold"), the answer of `-chc` and `-teq` is the intended one, since the invariant and the
   postcondition both hold. Making the modes agree requires either cutting the loop at its invariant in `Horn` and
   `TEQ` (losing what they infer), or making the refutation of a goal behind a given invariant `unknown` in
   `VCGen`, i.e., marking those goals `:abstract` as well, which revises the decision.

2. **`:status` cannot be passed to the solver.** z3 checks `(set-info :status sat)` itself and answers the next
   command with an error ("check annotation that says sat") after a contradicting `check-sat`. The solver sink
   drops it, also under `-check`, hence it is only metadata for Cuvée, not the SMT-LIB meaning of `:status`.

3. **The answers to the commands added by transforms are not what SV-LIB expects.** `Horn` adds a `check-sat` and
   `get-model` at `Done`; after a `verify-call` the sink acknowledges `Done` with `success` instead of no answer,
   such that `Pipe.run` does not report them (it reports the answers added in front of a command without answer).
   This relies on the rule of `Pipe.run` for added answers, and with `print-success` a `success` appears at the end.
   Obligations after the last `verify-call` are still checked, only not reported.

4. **The work is not done at `verify-call`.** The transforms emit the goals and clauses of a procedure when its
   definition is flushed, which in all current tasks is the `verify-call`, but not in general, e.g. after another
   query between `define-proc` and `verify-call`. Each answer covers all procedures so far, not those that the call
   reaches, and the aggregation makes an answer `incorrect` because of an earlier, unrelated call.

5. **`:abstract` is per procedure.** `VCGen` produces one goal per procedure, so a loop without invariant makes all
   obligations of the procedure `unknown`, also those that do not depend on the loop, which `-split` separates but
   which keep the attribute.

6. **`-verify` hides the output that other tools read.** `xml/cuvee.xml` and `xml/cuvee-fallback.xml` pass `-rules`
   for `scripts/rules.py`, which reads the `:used` of the printed goals; under `-verify` nothing is printed, the
   statistics are lost. Likewise the remaining goals, which explain an `unknown`, are no longer visible.

7. **`cuvee.py` needs `-verify`.** It reads only the answers, a run without `-verify` is an error; the archive of
   SV-COMP passes it (`archive/README.md`, `archive/smoketest.sh`), the options of the fm-tools entry
   (`data/cuvee.yml`) must as well.

8. **Errors of the options are exceptions.** `Config.validate` raises before the pipeline runs, like the existing
   errors of the command line, which are printed as `Exception in thread "cuvee" Error(...)` with a stack trace
   rather than as `(error ...)`, and cannot be examples with an expected `.err`.
