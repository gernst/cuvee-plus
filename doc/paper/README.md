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
the cloud runs of 0.53.26 on Oct 31, 2026 (`results/cuvee.teq05326-*` and
`results/cuvee-fallback.fb05326-*`: `xml/cuvee.xml` and `xml/cuvee-fallback.xml`, 120 s of CPU time,
1 core and 7 GB on an AMD Ryzen 7 PRO 5750G, far less than the 900 s, 4 cores and 15 GB of SV-COMP).
They are not scored: Cuvée's witnesses carry no invariants and no values of a violation yet, so its
results are not confirmed.

- The counts of Cuvée in the text are derived from the table and the runs: the fallback adds 7 proofs in
  Arrays and 11 in Loops (and loses 4 refutations of Loops at the time limit); the unsafe tasks are
  120 + 209 = 329, of which Cuvée refutes 63 + 37 = 100, and 63 + 33 = 96 with Z3.
- The figure of the rules (`rules-frequency.pdf`, under version control as an input of the paper) is
  `python3 scripts/rules.py --tools cuvee.teq05326`, from the run of Cuvée without Z3; the numbers of
  its paragraph are those of `rules.csv` (the totals) and `rules-unused.txt`.
- The paper gives no timings and no counts of error statuses (non-termination, frontend, fallback).

A new run updates the table and the figure: `./benchmark xml/cuvee.xml` (and the
`-fallback` variant), one call per task set (see CLAUDE.md), then `scripts/rules.py` as above.

## Open points

- The reference of MonoCera is `[TODO]`.
- The TEQ paper is cited as an anonymous submission under review; citing it
  from a paper with an author name may break its double-blind review.
- Cuvée's witnesses carry no invariants, so SV-COMP counts its proofs as
  unconfirmed (score 0); the paper says so.
- The section AI Declaration summarizes the share of the coding agents
  (counts of commits and lines from the git history).
- The body is about half a page over the usual 4 pages.
