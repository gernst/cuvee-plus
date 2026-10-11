# SV-COMP competition contribution

[cuvee.tex](cuvee.tex) is the competition contribution of Cuvée for SV-COMP
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
| Cuvée | 0.34.22 | `cuvee.2026-10-09_18-48-26` (Arrays), `cuvee.2026-10-09_18-46-59` (Loops, 6 tasks fewer) |
| Cuvée+Z3 | 0.35.2 | `cuvee-fallback.2026-10-10_10-44-55` (Arrays), `cuvee-fallback.2026-10-10_10-28-14` (Loops) |
| Symbiotic | SV-COMP 2026 | `symbiotic.2026-10-10_10-14-10` |
| AISE | SV-COMP 2026 | `aise.2026-10-10_10-50-01` |
| UAutomizer | SV-COMP 2026 | `uautomizer.2026-10-10_09-41-15` |
| CPAchecker | SV-COMP 2026 | `cpachecker.2026-10-10_09-41-16` (Arrays), `cpachecker.2026-10-10_09-39-19` (Loops) |
| Korn | SV-COMP 2026 | `korn.2026-10-10_11-59-02` |

- The latest `cuvee-fallback` files are runs of 1 min (0.35.5), which
  `common.latest` would pick; the table uses the 15 min runs above.
- "133 safe Arrays tasks within 2 min" of 0.35.16 is
  `cuvee-quick.2026-10-11_11-47-10` (`xml/cuvee-quick.xml`).
- The error counts of the weaknesses (140 tasks with "rewriting does not
  terminate", floats, `goto`, parse errors) are those of SV-COMP.md; the
  wrong proofs of Cuvée+Z3 are the 15 variants of `geo1-u` in Loops.
- The example of Fig. 1 was run with `-teq -simplify -rules`, which lists
  the 11 rules of its proof; a trivial program takes about 5 s CPU time.

A new run updates the table: `./benchmark xml/cuvee.xml` (and the
`-fallback` variant), one call per task set (see CLAUDE.md).

## Open points

- The affiliation is a guess, the Zenodo DOI of the tool archive and the
  reference of MonoCera are `[TODO]`, no license is stated.
- The TEQ paper is cited as an anonymous submission under review; citing it
  from a paper with an author name may break its double-blind review.
- Cuvée writes no witnesses, so SV-COMP counts its proofs as unconfirmed
  (score 0); the paper says so.
- The paper describes the configuration with Z3, whose 15 wrong proofs make
  the Loops score negative (−42, against +240 without Z3).
- The body is about half a page over the usual 4 pages.
