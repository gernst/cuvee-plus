# Trace equations for program verification (CPAchecker Workshop 2026)

- `story.md`: the storyline, for an audience that knows nothing about TEQs: two worlds and what lies between ("routine, not trivial"), then
  three claims (invariants are the wrong representation; insight belongs in reusable lemmas, and AI should make
  tools; reasoning must be incremental), each with its slides.
- `slides.tex`: the beamer deck that tells the story (16:10, 36 pages with overlays). Compile with
  `pdflatex slides.tex` (twice).

Slides from the earlier decks are embedded as full pages: `\cpa{page}` from `figures/CPA.pdf`, `\nextgen{page}` from
`figures/NextGeneration.pdf` (copies of `~/Papers/array-acceleration/talks/`). The slides with code examples are
redrawn in TikZ in the same look: Linux Libertine, code in Bera Mono, programs in boxes with callouts.

No evaluation results and no timings. The slide "How Cuvée is built" leaves a grey placeholder for the speaker's
own experience.

The PDFs are ignored by the repository (`*.pdf` in `.gitignore`). Commit `figures/*.pdf` with `git add -f`.
