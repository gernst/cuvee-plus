# Anonymization

Places in the repository that identify the author, found on Oct 13, 2026 by a search of all tracked files
(and of the untracked `pending/` and `benchmarks/loopannotator/`). Nothing has been changed yet.

## Name, email, affiliation, photo

| Where | What |
|---|---|
| `src/cuvee/Config.scala:433` | `copyright()` prints `Gidon Ernst <gidon.ernst@gmail.com>` (visible in the tool's output) |
| `scripts/zenodo.py:67-77` | name, "Ludwig Maximilian University of Munich", ORCID, copyright line, `github.com/gernst/cuvee-plus` |
| `doc/paper/cuvee.tex:41-44, 303-304` | author, LMU, email; "developed by Gidon Ernst at LMU Munich" |
| `doc/paper/references.bib:66-71` | self-citation `Ernst, Gidon` with the GitHub URL |
| `doc/array-algorithms/array-algorithms.tex:42` (and the PDF) | author, LMU, email; lines 91-103 tie the author to the TEQ paper ("the author and his coauthors") |
| `doc/state-traces/state-traces.tex:44` | author, LMU, email |
| `doc/cpa-workshop/slides.tex:108` | name, "LMU Munich, University of Regensburg", sosy-lab people page |
| `doc/cpa-workshop/slides.tex:604-623` | "[Coenen, Ernst, submitted 2026]" (the TEQ paper, names the co-author), "[Ernst, Fedyukovich, iFM 2025]" |
| `doc/cpa-workshop/figures/photo.jpg` | portrait photo of the author, on the title slide |
| `benchmarks/acsl/array-patterns/README.txt:11` | "Marian Lingsch-Rosenfeld and Gidon Ernst" |

## Account handle and links that resolve to the author

- `github.com/gernst/cuvee-plus`: `README.md:50`, `archive/README.md:9`, `cuvee.py:32`;
  `github.com/gernst/benchexec`: `TODO.md:61`.
- Zenodo DOI `10.5281/zenodo.23317707` (the record shows the name): `README.md:35`, `README.md:257`,
  `TODO.md:52`; the record id in `scripts/zenodo.json`.
- Pull/merge requests opened by the author: `sosy-lab/benchexec#1327` (`README.md:240`, `TODO.md:60`),
  fm-tools `!1176` (`TODO.md:52`).

## Paths and infrastructure

- `/home/ernst/...`: `.vscode/launch.json:9`, `benchmark:3`.
- Untracked: hard-coded `/home/ernst/...` paths in about ten scripts of `pending/acsl/` (`check.sh`,
  `check1.sh`, `show.sh`, `annotate.py`, `specs/*.py`).
- Weak signal: the VerifierCloud and `vcloud-benchmark.py` (the LMU SoSy-Lab cluster) in `doc/benchmarks.md`,
  `CLAUDE.md`, `ideas/experiments.md`.

## Outside the files

- Git history: 675 commits by `Gidon Ernst <gidon.ernst@sosy.ifi.lmu.de>`, one by
  `gidon.ernst@gmail.com`; remote `git@github.com:gernst/cuvee-plus.git`. Anything shipped with `.git`
  reveals these.
- The tool name Cuvée is public and linked to the author through SV-COMP, fm-tools and Zenodo; mentions of
  the SV-COMP tool entry (`README.md`, `TODO.md`) strengthen the link. Only a rename avoids it.

## Not an issue (third parties)

- SPDX/copyright headers in `benchmarks/acsl/**` (Beyer, Dangl, ...), `cuvee.py:4`, the `LICENSE.*` files.
- `sosy-lab` URLs of sv-benchmarks, BenchExec, SV-COMP results, and the DTDs in `xml/*.xml`.
- `/home/usea`, `/home/zafer`, `/home/cav23` in `benchmarks/monocera/original_logs_from_paper/` and
  `benchmarks/monocera/run-list/` (the MonoCera authors).
- No image or PDF other than `photo.jpg` carries author or GPS metadata.

## Suggested procedure for an anonymous artifact

1. Export without history: `git archive HEAD | tar -x -C <dir>`.
2. Drop `doc/`, `.vscode/`, `scripts/zenodo.py`, `scripts/zenodo.json`.
3. Scrub `src/cuvee/Config.scala`, `README.md`, `TODO.md`, `cuvee.py`, `archive/README.md`, `benchmark`,
   `benchmarks/acsl/array-patterns/README.txt`.
4. Re-run the search on the export:
   `grep -rIn -i -E 'gidon|ernst|gernst|lmu|ludwig|orcid|zenodo\.2331|/home/ernst|benchexec#1327|!1176' <dir>`.
