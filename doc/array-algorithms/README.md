# Cuvée: Verifying Array Programs by Trace Equation Systems and a Lemma Database

[array-algorithms.tex](array-algorithms.tex) describes the approach of Cuvée as it is implemented: the representation of
loops as trace equation systems (`-teq`, one trace per strongly connected component), the deduction engine (`-prove`)
and the lemma database with the insights behind them, the tool around them (frontends, `-fallback`, `-chc`, `-verify`),
one proof followed step by step (the array initialization), worked examples (linear search, the swap of two arrays,
nested loops and the transpose, binary search and the lower bound, selection sort, bubble sort, gnome sort, the merge,
the distinctness check, the MonoCera tests of [benchmarks/monocera](../../benchmarks/monocera)), the migration of the
algorithms of [examples/dafny/algorithms](../../examples/dafny/algorithms) to the closed form and the three that stay
open, the evaluation, the principles of writing lemmas for lookup, and the insights. It replaces the former documents
`doc/overview` (the overview of the approach), `doc/state-traces` (three examples step by step), and `doc/monocera`
(the first lemmas for the MonoCera tests). `array-algorithms.pdf` is the compiled document.

The examples run by the command line in the first line of each file (`examples/dafny/algorithms`,
`examples/dafny/teq`); the numbers of the evaluation are those of the TEQ paper (`doc/array-acceleration`).

## Files

- `array-algorithms.tex`: preamble, introduction (with the tool), notation, the order of the sections, the AI declaration.
- `teq.tex`: trace equation systems (combinators, the partition into components, closed nested loops, choices, exits).
- `engine.tex`: the engine, each capability with the insight it answers, and what lies beyond rewriting.
- `database.tex`: the lemma database, its modules, the kinds of lemmas, and the proofs in Lean.
- `init.tex`: the array initialization, from the verification condition to the closed goal.
- `lsearch.tex`, `swap.tex`, `nested.tex`, `bisection.tex`, `sorts.tex`, `monocera.tex` (with
  `monocera-table.tex`): the worked examples.
- `open.tex`: the migration of seven algorithms to the closed form, the limits of the engine it ran into, and the
  three algorithms that stay open.
- `evaluation.tex`: SV-COMP, MonoCera, SV-LIB, Rapid, the use of the lemmas, and annotations per task.
- `principles.tex`, `conclusion.tex`: the principles and the insights, with the limitations.

## Build

```
pdflatex array-algorithms.tex; pdflatex array-algorithms.tex
```

No bibliography.
