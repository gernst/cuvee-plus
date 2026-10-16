# Review of the story (October 13, 2026)

Open points from re-reading `story.md` against the slides and the state of the repository, and how they were
addressed.

## 1. The binary search (done)

The slide follows the binary search of `doc/array-algorithms` (formerly `doc/state-traces`): the binary search over a sorted array, one lemma about the bisection for the
whole loop, its bounds as forward facts through the partition points `lower` and `upper`. The caption says the
lemmas are general, assumed, and not yet in the database.

## 2. Claim 3 as incremental (done)

The slide "Incremental reasoning on TEQs" names the incremental step of each example: the two loops (the second
builds on the summary of the first), the swap (one question at a time), nested loops (the inner loop first), the
binary search (bounds while the number of iterations stays unknown).

## 3. Where the induction went, and what is checked (done)

"Variable-modular, not state-modular" says that there is no induction per program: it is in the lemmas of the
database, proved once. The thesis slide notes that lemmas written for one program are assumed unless proved, and
the binary search's caption says its lemmas are assumed.

## 4. The evidence for "AI should make tools" (done)

"How Cuvée is built" and "What the AI contributed" state the speaker's experience: the cost, the models, the
division of labour, and the AI's contributions to the approach. The Lean slide frames `grind` as a better tool
built by people: a better tool beats a better proof.

## 5. Smaller points (done, one open)

- `story.md` follows the slides in order and no longer refers to pages of a removed PDF.
- "Questions for this community" frames TEQs as complementary to model checking (TEQ summaries as acceleration in a
  CPA), and the witness question mentions the lowering to quantified invariants.
- A references slide closes the talk.
- **Open:** the slide "Evaluation" is a placeholder table; its numbers come from the runs with one version of Cuvée.
  The task counts in it mix sources (the submission counts 150 MonoCera tasks, `ideas/experiments.md` 125).
