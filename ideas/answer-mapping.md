# Answers mapped back by the transforms

Rejected (Oct 22, 2026). Replaced by goals and lemmas that flush and are answered immediately, see
[doc/architecture.md](../doc/architecture.md), "Answers".

## Proposal

Each command of the input has exactly one response, as in SMT-LIB: a transform maps the answers to its output
back to the answers to its input, e.g. `Split` combines the answers to the parts of a goal (incorrect if one part
is, unknown if one is undecided, correct if all are), `Simplify` answers the goals that it drops correct, `VCGen`
answers a procedure by its goals and revises `incorrect` to `unknown` for a loop without invariant.

## Why not

- Goals are declarations, which a stage buffers, so the answers to several goals came back together with the next
  flush, and each transform had to return its output per command to find the answers that belong to a goal.
- Goals generated from commands that are no obligations, e.g. the goals of a procedure, have no place among the
  answers to the input, so the mapping had to move their answers behind those of the input to keep the answers
  of the stages above aligned.
- An approximation is visible in the goal itself, `:abstract`, so the sink revises the answer, not the transform.

## Instead

- A goal or a lemma that is not free flushes: the stage passes on the pending declarations, then the goal on its
  own, and its answer combines the answers to its outputs (`Stage.combine`), which needs no alignment. A goal that
  a transform drops, since it has reduced it to `true`, has no outputs and is `correct`.
- Free lemmas are assumptions: they are acknowledged like axioms and do not flush; answering them `correct` would
  make a run whose goals have no answer, e.g. without solver, look proved by the lemma database.
- The goals of procedures are answered at the next flush, one answer each; consumers read the answers as a set.
- `Horn` checks at `Done` only, since a CHC solver takes one problem with one `check-sat` (Spacer, Eldarica, and
  Golem support neither `push`/`pop` nor `reset` reliably); with `-verify` the answer to the `check-sat` is that
  of the program (`Horn.report`). A transform still may consume the flush (`Horn` the `verify-call`).
