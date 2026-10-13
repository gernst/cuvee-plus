# Trace equations for program verification (CPAchecker Workshop 2026)

- `story.md`: the storyline, for an audience that knows nothing about TEQs: two worlds and what lies between
  ("routine, not trivial"), then three claims (invariants are the wrong representation; insight belongs in reusable
  lemmas, and AI should make tools; reasoning must be incremental), each with its slides.
- `review.md`: points from re-reading the story against the slides and the repository, and how they were addressed.
- `slides.tex`: the beamer deck that tells the story (16:10, 40 pages with overlays). Compile with
  `pdflatex slides.tex` (twice).

All slides are drawn in beamer and TikZ, in the look of the earlier decks (`~/Papers/array-acceleration/talks/CPA.pdf`
and `Next Generation.pdf`): Linux Libertine, code in Bera Mono, programs in boxes with callouts. The pictures in
`figures/` are taken from those decks:

- extracted: `photo.jpg`, `svcomp.jpg` (the SV-COMP plot), `aws.jpg`, `datadog.jpg`, `meme.jpg` (the code on its
  sheets is set on the slide), `checkmark.jpg`, `unicorns.png`, `wand.png`, `lean.png` (the generated proof);
- rendered from the vector graphics of the title page: `logos.png`.

No evaluation results and no timings. The slide "How Cuvée is built" leaves a grey placeholder for the speaker's
own experience.
