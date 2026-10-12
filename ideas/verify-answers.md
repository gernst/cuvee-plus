# Answers `correct`/`incorrect`/`unknown` with `-verify`

Proposal of Oct 12, 2026 (after 0.39.7 renamed the former `-verify` to `-vcgen`), implemented in 0.41.0 as
revised and simplified (see below): `-z3` and `-cvc5` choose the solver, which checks as before, `-verify` answers
with the sink [pipe/Verify.scala](../src/cuvee/pipe/Verify.scala), the answers are aggregated over all obligations
so far, given to each `verify-call` and to the end of an input without `verify-call`, goals are expected valid and
each `check-sat` satisfiable (see [doc/architecture.md](../doc/architecture.md)).

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
- `determine_result` reads the answers: any `incorrect` is false (`RESULT_FALSE_PROP`, for every property),
  at least one answer and all `correct` is true, otherwise unknown; no
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
- `-z3` and `-cvc5` choose the solver, which checks the output as before (a goal that does not hold is an error,
  `check-sat` and `get-model` are answered); `-verify` builds the sink
  [pipe/Verify.scala](../src/cuvee/pipe/Verify.scala) instead. `Config.receiver` builds the sink from the final
  configuration.
- The sink checks each obligation against the status that it has if the program is correct (`Verify.expected`:
  goals and lemmas `unsat` of their negation, `check-sat` `sat`), aggregates the outcomes over the whole run, and
  answers each `verify-call`, and `Done` if there was no `verify-call`; procedures that reach it are an error. The
  commands go to the solver directly. `Pipe`, `Stage`, `Sink` and the passive sinks are unchanged.
- `VCGen` marks the goal of a procedure `:abstract` if one of its loops has no invariant, `Fallback` the goals it
  lowers.
- `cuvee.py` reads only the answers under `-verify`; the definitions in `xml/` pass `-verify`.
- Examples in `examples/{c,svlib,smtlib}/verify`, a unit test of the options and of the classification; the
  expected outputs of `-fallback` regenerated for `:abstract`.

### Problems

1. **The modes differ on a loop invariant that holds but is too weak** (accepted). In
   `examples/svlib/vcgen/invalid_invariant.svlib` (and `examples/c/verify/vcgen_weak_invariant.c`), `-vcgen`
   answers `incorrect`, since the invariant is the only summary of the loop, but `-chc` and `-teq` answer
   `correct`, since they extend the given invariant by the ones they generate: `Horn` checks the invariant at the
   loop head and infers its own for the postcondition, `TEQ` summarizes the loop by its trace. With an invariant
   generator, extending the invariants is intended.

2. **`:status` cannot be passed to the solver** (resolved by simplification 4). z3 checks `(set-info :status sat)`
   itself and answers the next command with an error after a contradicting `check-sat`; `Horn` no longer writes it,
   the polarity of `check-sat` is that of `Verify.expected`.

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

6. **`-verify` hid the output that other tools read** (resolved in 0.41.2 for `-rules`). `scripts/rules.py` read the
   `:used` attributes of the printed goals. Now each `-simplify` reports its applications after each assertion as
   `(set-info :used ((name count) ...))`, which the solver sink and the verify sink print on stderr instead of
   passing it to the solver (z3 rejects structured values of `set-info`, contrary to SMT-LIB). The remaining goals,
   which explain an `unknown`, are still not visible under `-verify`.

7. **`cuvee.py` needs `-verify`.** It reads only the answers, a run without `-verify` is an error; the archive of
   SV-COMP passes it (`archive/README.md`, `archive/smoketest.sh`), the options of the fm-tools entry
   (`data/cuvee.yml`) must as well.

8. **Errors of the options were exceptions** (resolved by simplification 2). `Config.validate` raised before the
   pipeline ran; now procedures that reach the verify sink are an error of the pipeline, reported as `(error ...)`
   (`examples/c/verify/invalid_no_transform.c`).

## Simplifications (implemented)

1. **No `-check`.** A solver without `-verify` checks, the option, the field `check`, and their rejections are
   redundant.
2. **No `Config.validate`.** The verify sink raises an error for `define-proc`, `declare-var`, and `annotate-tag`,
   which a transform (`-vcgen`, `-teq`, `-chc`) eliminates, instead of answering them `unsupported` and the input
   `correct` without checking anything; inputs with their own goals get answers without a transform. `-print` and
   `-o` with `-verify` need not be rejected, the printer is not used.
3. **Goals are checked after `incorrect` as well.** The sink does not skip the remaining goals once the outcome is
   `incorrect`, such that every obligation is checked and diagnosed, at the cost of solver time on unsafe programs.
4. **The polarity of `check-sat` by kind instead of `:status`.** Under `-verify`, every `check-sat` counts with
   expected `sat`, since only `-chc` produces one: no `set-info` in `Horn` and its outputs, no special case for
   `:status` in the solver sink, no field `expected` in the verify sink. The flip is stated once, by
   `Verify.expected(cmd)`: goals and lemmas `unsat` (of their negation, see `Solver.valid`), `check-sat` `sat` (a
   model of the clauses gives the invariants); `Horn` refers to it at the `check-sat` it adds, and
   doc/architecture.md describes it. An input's own `check-sat` counts as well.

Kept: answering `Done` only without `verify-call` (`answered`, acknowledged with `success`), `:abstract` in `VCGen`
and `Fallback`.
