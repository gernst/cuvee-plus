# Trace Equation Systems for Array Algorithms: Worked Examples

[array-algorithms.tex](array-algorithms.tex) documents the examples of
[examples/dafny/algorithms](../../examples/dafny/algorithms) in the style of
the TEQ paper: for each program the trace equation system, the lemmas, their
instantiation, and the idea; then the proofs of some of the MonoCera tests
([benchmarks/monocera](../../benchmarks/monocera)) re-traced, and a summary of
the principles. One file per example (`lsearch.tex`, `selection_sort.tex`,
...), included by the main file; `array-algorithms.pdf` is the compiled
document, rebuilt with the sources.

## Build

```
pdflatex array-algorithms.tex; pdflatex array-algorithms.tex
```

No bibliography. The findings that the sections cite by number are those of
[NOTES.md](../../examples/dafny/algorithms/NOTES.md) of the examples.
