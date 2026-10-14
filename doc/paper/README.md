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
of that page. AISE did not participate in ReachSafety-Arrays. The tasks are
the valid ones of SV-COMP 2026: the 13 void tasks of Arrays (category
`missing` in the official files) are left out, which leaves 427 tasks (314
safe) and 764 (555 safe). The results of Cuvée are ours, with BenchExec
(900 s CPU time as in SV-COMP, but 7 GB and 2 cores of an Intel Core i7-6700 instead of 15 GB and 4),
not scored, since Cuvée produces no witnesses (the table gives no scores since Oct 14, 2026); the counts are
those of `scripts/common.py` (`load`).

| Column | Version | Result files |
|---|---|---|
| Cuvée (TEQ) | 0.46.9, `-verify`, the migrated modules | `results/cuvee.2026-10-13_22-11-17` (Arrays), `results/cuvee.2026-10-13_22-11-21` (Loops) |
| Cuvée+Z3 (TEQ) | 0.46.9, `-verify`, the migrated modules | `results/cuvee-fallback.2026-10-13_22-11-26` (Arrays), `results/cuvee-fallback.2026-10-13_22-11-29` (Loops) |
| Others | SV-COMP 2026 | `scripts/official/<tool>.*.fixed.xml.bz2` |

- The paper names no version of Cuvée. The table was updated on Oct 14, 2026 with the runs of 0.46.9, after the
  migration of the lemma database (one trace per strongly connected component, `-prove`), which include the
  migrated modules (`-include teq:aggregation` ... `teq:unsigned`, `xml/cuvee.xml`), a second round of `-split
  -prove` (not for Cuvée+Z3) and `-rules`, unlike the command of the archive; the rows of Cuvée are computed by
  `scripts/paper.py`, which reproduces the earlier numbers of 0.41.4 from those runs. The text of the paper still
  describes the simplifier of the competition version in places.
- "Unique" counts the safe tasks that Cuvée proves and that no other tool
  reports as true in the official results, confirmed or not.
- The error counts of the weaknesses ("rewriting does not terminate",
  floats, `goto`, parse errors, limits of the fallback, timeouts) are the
  statuses of the runs of Cuvée on the valid tasks of both categories. The
  wrong results of 0.41.4 (Cuvée+Z3: the 7 variants of `fermat1-ll_unwindbound`,
  `sanfoundry_24-1` and `verifythis/lcp`) are fixed since 0.42; the runs of
  0.46.9 have none.
- The example of Fig. 1 was run with `-teq -simplify -rules`, which lists
  the 11 rules of its proof; a trivial program takes about 7 s CPU time
  (measured on Oct 12, 2026).

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
