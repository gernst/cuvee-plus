# SV-COMP competition preview

[cuvee.tex](cuvee.tex) is the competition preview of Cuvée for SV-COMP
(LNCS, `llncs` with `splncs04`, about 4.5 pages without references);
[references.bib](references.bib) its bibliography. `cuvee.pdf` is not under
version control.

## Build

```
pdflatex cuvee.tex; bibtex cuvee; pdflatex cuvee.tex; pdflatex cuvee.tex
```

bibtex refuses to write outside the current directory, so build in this
directory or copy both files to a build directory first.

## Sources of the numbers

The results of Symbiotic, AISE, UAutomizer, CPAchecker, and Korn are taken
literally from the official results of SV-COMP 2026 (`scripts/official`, the
`.fixed` files of https://sv-comp.sosy-lab.org/2026/results/results-verified/,
which count confirmed results only); their scores agree with the score table
of that page. AISE did not participate in ReachSafety-Arrays. The results of
Cuvée (440 tasks of Arrays, 320 safe, and 764 of Loops, 555 safe) are those of
the TEQ paper (`doc/array-acceleration`, imported from `scripts/out/experiments.pdf`
on Oct 15, 2026), with BenchExec (900 s CPU time as in SV-COMP, but 7 GB and 2 cores
of an Intel Core i7-6700 instead of 15 GB and 4). They are not scored: Cuvée writes
witnesses, but empty ones for now, so its results are not confirmed.

- The paper names no version of Cuvée. Its text still describes the simplifier of the competition version in
  places.
- The counts of Cuvée in the text are derived from the table: the fallback adds 230 - 149 = 81 proofs in Loops;
  the unsafe tasks are 120 + 209 = 329, of which Cuvée refutes 9 + 16 = 25, and 48 + 20 = 68 with Z3.
- The paper gives no timings and no counts of error statuses (non-termination, frontend, fallback), which were
  not rechecked for these runs.

A new run updates the table: `./benchmark xml/cuvee.xml` (and the
`-fallback` variant), one call per task set (see CLAUDE.md).

## Open points

- The reference of MonoCera is `[TODO]`.
- The TEQ paper is cited as an anonymous submission under review; citing it
  from a paper with an author name may break its double-blind review.
- Cuvée writes no witnesses, so SV-COMP counts its proofs as unconfirmed
  (score 0); the paper says so.
- The section AI Declaration summarizes the share of the coding agents
  (counts of commits and lines from the git history).
- The body is about half a page over the usual 4 pages.
