# Answers `correct`/`incorrect`/`unknown` with `-verify`

Proposal, not implemented (Oct 12, 2026, after 0.39.7 renamed the former `-verify` to `-vcgen`).

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
