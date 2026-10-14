# Trace Equation Systems for Array Algorithms: Worked Examples

[array-algorithms.tex](array-algorithms.tex) documents the examples of
[examples/dafny/algorithms](../../examples/dafny/algorithms) in the style of
the TEQ paper: for each program the trace equation system, the lemmas, their
instantiation, and the idea; then the proofs of some of the MonoCera tests
([benchmarks/monocera](../../benchmarks/monocera)) re-traced, and a summary of
the principles. One file per example (`lsearch.tex`, `selection_sort.tex`,
...), included by the main file; `array-algorithms.pdf` is the compiled
document, rebuilt with the sources.

The document describes the state of Oct 11, 2026: `-teq -simplify` on one trace per variable, with the
fragments of inner loops of the module `teq:nested`. Since Oct 13, `-teq` makes one trace per strongly
connected component and closes nested loops, `-prove` replaces `-simplify`, and `teq:nested` is retired to
`resources/cuvee/legacy` (Oct 14); the nested sorts leave one goal each now, cocktail_sort does not terminate
(the status lines of the examples). The document is not rewritten until the approach has converged.

## Build

```
pdflatex array-algorithms.tex; pdflatex array-algorithms.tex
```

No bibliography. The findings that the sections cite by number are those of
[NOTES.md](../../examples/dafny/algorithms/NOTES.md) of the examples.
