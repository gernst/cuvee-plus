# Review of the story (October 13, 2026)

Open points from re-reading `story.md` against the slides and the state of the repository. The arc holds:
problem, three claims, approach, open questions.

## 1. The binary search (done)

The slide now follows `doc/state-traces`: the binary search over a sorted array, one lemma about the bisection for
the whole loop, its bounds as forward facts through the partition points `lower` and `upper`. The caption says the
lemmas are general but not yet in the database.

## 2. Claim 3 is not yet shown as incremental

The swap, nested-loop and binary-search slides show that the representation stretches further, but none of them
shows the incrementality the claim promises. Either:

- add one line per example that names the incremental step: the number of iterations stays unknown and the bounds
  still follow; the inner loop is summarized first and becomes one value of the outer update; or
- rename the claim to "Reasoning must be incremental and compositional". The sum example, where the second loop
  builds on the first loop's result, is the cleanest demonstration and could open claim 3.

## 3. "Where did the induction go?"

This is the obvious question from a model-checking audience. Answer: the induction moved into the database lemmas,
which are proved once; the TEQ itself is an exact description of the loop. A sentence in claim 1, or a backup
slide, would pre-empt it.

Related: the thesis slide says "checked once (Lean, …)". That holds for the database, but not for program-specific
lemmas such as those of the binary search, which are assumed. Say this caveat, at least verbally.

## 4. The evidence for "AI should make tools" is thin

- "How Cuvée is built" still has the grey placeholder; the thesis rests on the speaker's experience there.
- The `grind` one-liner shows a better tool beating a generated proof. But `grind` was built by people, not by AI.
  The argument still holds (tools beat per-program proofs), but frame it that way, so it is not read as evidence for
  AI-made tools.

## 5. Smaller points

- Done: `story.md` follows the slides in order and no longer refers to pages of the removed `figures/CPA.pdf`.
- Partly done: the slide "Evaluation" is a placeholder table; the numbers come from the runs with one version.
- "Search rediscovers known facts" is aimed at exactly this audience's tools. Acceleration is known in their
  community too, so "complementary" may land better than "inference is bad".
- The witness question is fair but non-trivial: correctness witnesses need state invariants, and TEQ normal forms
  would first have to be lowered to quantified invariants.
