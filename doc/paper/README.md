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

All runs are ours, with BenchExec on the C versions of the tasks
(`results/`, the categories ReachSafety-Arrays and ReachSafety-Loops,
15 min unless stated otherwise). The expected verdicts are those of the yml
files of `sv-benchmarks`, the counts are those of `scripts/common.py`
(`collect`, `load`), the score is that of SV-COMP without the validation of
witnesses.

| Column | Version | Result files (`results/<prefix>.results.SV-COMP27_unreach-call...`) |
|---|---|---|
| Cuvée | 0.41.4, `-verify`, all modules | `cuvee.2026-10-12_12-48-00` (Arrays), `cuvee.2026-10-12_13-03-58` (Loops) |
| Cuvée+Z3 | 0.41.4, `-verify`, all modules | `cuvee-fallback.2026-10-12_13-15-47` (Arrays), `cuvee-fallback.2026-10-12_13-24-45` (Loops) |
| Symbiotic | SV-COMP 2026 | `symbiotic.2026-10-10_10-14-10` |
| AISE | SV-COMP 2026 | `aise.2026-10-10_10-50-01` |
| UAutomizer | SV-COMP 2026 | `uautomizer.2026-10-10_09-41-15` |
| CPAchecker | SV-COMP 2026 | `cpachecker.2026-10-10_09-41-16` (Arrays), `cpachecker.2026-10-10_09-39-19` (Loops) |
| Korn | SV-COMP 2026 | `korn.2026-10-10_11-59-02` |

- The paper names no version of Cuvée. The runs of Cuvée include the modules
  `nested`, `sorting`, and `strides` of the lemma database (`-include`) and
  `-rules`, unlike the command of the archive.
- The error counts of the weaknesses ("rewriting does not terminate",
  floats, `goto`, parse errors, limits of the fallback, timeouts) are the
  statuses of these runs, over both categories; the wrong results of
  Cuvée+Z3 are the 7 variants of `fermat1-ll_unwindbound` (wrong true) and
  `sanfoundry_24-1` and `verifythis/lcp` (wrong false).
- The example of Fig. 1 was run with `-teq -simplify -rules`, which lists
  the 11 rules of its proof; a trivial program takes about 5 s CPU time.

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
