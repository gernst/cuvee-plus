# Answers mapped back by the transforms

Proposal, not implemented (Oct 21, 2026, after `Transform` returned an optional flush in 0.47.0).

## Problem

A stage rewrites the commands on their way down, but the answers come back up unchanged: the answer to a command
is the next sink's answer to the command that the stage passes on, and the answers to the queries that a
transform adds in front of it travel separately (`Sink.query(cmds, last)`, the "added" answers), reported by
`Pipe.run` only if the command has no answer of its own. Since a transform may replace or consume the flushing
command (`Horn` consumes the `verify-call`), the next sink's answer is no longer the answer to the input command,
and the reporting rule is arbitrary: a consumed flush is acknowledged with `success` by the stage.

## Principle

As in SMT-LIB, each command of the input has exactly one response, and whoever rewrites a command is responsible
for its response. A transform maps in both directions: the commands for the flush, and how the answers to the
queries among them become the answer to the flush.

```scala
type Transform = (Config, State, List[Cmd], List[Cmd], Cmd) => (List[Cmd], List[Result] => Result)
```

- Most transforms pass the flush on and take its answer (`answers => answers.last`).
- `Done` is not part of the input and has no answer of its own; its response is the one place where several
  answers are legitimate, e.g. `sat` and the model of `-chc -z3` (a list for `Done` only).
- Answers translated back belong here as well, e.g. the model of `-chc` in the language of the input, now a special
  case of the solver sink.

`Sink.query(cmd)` returns `(Result, Sink)`, the stage folds its batch through the next sink and applies the
mapping; the added answers and the reporting rule of `Pipe.run` disappear. Only the results of the top-level
stage are reported.

## Constraint of CHC solvers

Spacer, Eldarica, and Golem take one complete problem with one `check-sat`: neither `push`/`pop` between queries
nor `reset` work reliably. Hence `Horn` cannot answer a `verify-call` when it occurs: it sends the entry clauses
and answers nothing, and its mapping at `Done` turns the answer to the single `check-sat` into the answer to the
call (`sat` correct, `unsat` incorrect, `unknown` unknown). This is exact for at most one `verify-call` at the end
of the input, as assumed now; for several, one `check-sat` decides only their conjunction (`unsat` cannot say
which call fails). One complete problem per call would answer each, at the cost of solving everything again.

## Consequences for `-verify`

The interpretation of the solver's answers moves from `pipe.Verify` (`Verify.expected`, the aggregated outcome)
into the transforms that know what their obligations mean: `Horn` maps `sat`, `VCGen` and `TEQ` the validity of
their goals per `verify-call`. Open with it: the unit of an answer (the obligations of one call rather than all so
far, the outcome reset after answering), obligations after the last `verify-call`, which are checked but never
answered, and `-vcgen` checking every procedure instead of what a call reaches. The tests that read solver answers
from the list of `Pipe.run` use `Report.collect` instead, and `Pipe.run` returns only the errors.
