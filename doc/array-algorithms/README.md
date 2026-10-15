# Array Algorithms by Lemma Lookup: Worked Examples

[array-algorithms.tex](array-algorithms.tex) shows what it takes to verify array programs by lookup in a database of
lemmas, with trace equation systems (`-teq`) and the deduction engine (`-prove`): the representation of loops, the
design of the engine and the insights behind it, worked examples (linear search, nested loops and the transpose,
binary search and the lower bound, selection sort, bubble sort, gnome sort, the merge and the distinctness check,
the MonoCera tests of [benchmarks/monocera](../../benchmarks/monocera)), the
algorithms of [examples/dafny/algorithms](../../examples/dafny/algorithms) that are not proved with what each needs,
the principles of writing lemmas for lookup, and the insights. `array-algorithms.pdf` is the compiled document,
rebuilt with the sources.

The results are those of reruns on Oct 14, 2026, with the command line in the first line of each example
(`examples/dafny/algorithms`, `examples/dafny/state`) and, for the MonoCera tests, the options of the run definition
`MonoCera_unreach-call` of `xml/cuvee.xml` with a 60 s limit (`monocera-table.tex`).

## Files

- `array-algorithms.tex`: preamble, introduction, notation, the order of the sections, the AI declaration.
- `teq.tex`: trace equation systems (combinators, the partition into components, closed nested loops, choices).
- `engine.tex`: the engine and the lemma database, each capability with the insight it answers.
- `lsearch.tex`, `swap.tex`, `nested.tex`, `bisection.tex`, `sorts.tex`, `monocera.tex` (with
  `monocera-table.tex`): the worked examples.
- `open.tex`: the algorithms that are not proved, and what they need.
- `principles.tex`, `conclusion.tex`: the principles and the insights.

## Build

```
pdflatex array-algorithms.tex; pdflatex array-algorithms.tex
```

No bibliography.
