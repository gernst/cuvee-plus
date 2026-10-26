# Can -slice prove tasks?

`-slice` simplifies procedures by symbolic execution, with the trace equation system of each loop at its head
(doc/prove.md, "Programs"). An assertion that simplifies to `true` disappears from the output, so a procedure without
assertions left is proved. The experiment (Oct 26, 2026): how much of what `-teq` proves does `-slice` prove alone?

## Measured

A prototype answered each procedure `correct` if no assertion was left, and the procedure had nothing that the
simplification assumes unchecked (postconditions, invariants of its loops, checks of tags, preconditions of its
callees), `unknown` otherwise, never `incorrect`. Cloud, 120 s, one core, 0.52.6 prototype, against `-teq -prove` of
0.52.4 (true/false):

| Set | -teq | -slice | only -slice | only -teq |
|---|---|---|---|---|
| MonoCera-Forall | 64/0 | 51/0 | 0 | 13 |
| MonoCera-Max | 2/0 | 0/0 | 0 | 2 |
| MonoCera-Min | 6/0 | 4/0 | 0 | 2 |
| MonoCera-Sum | 17/0 | 17/0 | 0 | 0 |
| Arrays | 137/62 | 105/0 | 0 | 32 |
| Loops | 218/29 | 137/0 | 3 | 84 |

`-slice` proves about three quarters of what `-teq` proves; only array_2-2-simple, divbin_unwindbound1 and
divbin2_unwindbound1 (Loops) are proved by `-slice` alone; Loops has 238 timeouts. Where `-teq` wins, it splits its
goals (`-prove -split -prove`) and decides the whole goal at once, where `-slice` decides each assertion under the
context of its position, e.g. sum_by_3_abstracted. The prototype was not kept: `-slice` answers nothing.

## Why -slice cannot answer on its own

- Only goals and lemmas that are not free, `check-sat`, and the `verify-call` of SV-LIB are answered `correct`,
  `incorrect` or `unknown`; every other command, procedures included, is acknowledged (`Sink.passive`). A stage
  combines the answers to the outputs of a goal into the answer to that goal (`Stage.combine`, which is how `-split`
  and flattening aggregate); the answers to goals among the outputs of a declaration come along at a flush.
- The obligations of a C program are implicit in its procedures, so each method makes up the goals that carry its
  answer: `-vcgen` one per procedure, `-teq` one for the entry point (`Config.entry`), `-chc` a `check-sat` from the
  entry point. The program itself is never what is answered; `cuvee.py` and the witness take the set of answers.
- So `-slice` answers only if it emits a goal (the prototype: a goal `true`, or `false` and `:abstract`, after each
  procedure), or if a stage may answer a declaration (a change of `Stage` and the sinks). Without either, a task gets no
  answer, which `cuvee.py` reports as an error, not as unknown.

## Ideas

- **The program as the unit of answer.** A declaration with obligations, the entry point or a procedure with
  assertions, answered like a goal, into which the stage aggregates the answers of its outputs; `-slice` would answer
  from the simplified procedure, `-vcgen`, `-teq` and `-chc` through their goals, which become an implementation
  detail of each method.
- **The entry point.** Consistent with `-teq` and `-chc`, `-slice` would answer the entry point only, `correct` if no
  assertion is left in it nor in the procedures that it reaches (whose assertions it does not check at the calls).
- **`incorrect`.** An assertion that simplifies to `false` is no violation: its context may be inconsistent without the
  engine noticing. `-teq` is sound there because it decides the whole goal `∀ choices. premises ⇒ assertion`, which is
  `false` only if the premises simplify to `true`, or refuted by `Eval` at values that satisfy them. `-slice` could do
  the same with the goal `∀ choices. facts ⇒ false` of the context of such an assertion.
- **The fallback inlined.** The assertions that remain lowered with their context and checked by z3 inside `-slice`,
  instead of a separate pipeline.
