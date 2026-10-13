# Story: Trace equations for program verification

CPAchecker Workshop, October 16, 2026. The storyline of the talk, in the order of the slides (`slides.tex`). The
audience knows verification, mostly the automated side, and nothing about TEQs. Open points are in `review.md`.

## Opening

- **Two worlds.** Automated verification (SV-COMP, CPAchecker): push-button, scales, simpler properties, the
  insight found by search. Interactive verification (KeY, AWS authorization): expressive specifications, the insight
  from a person. Their strengths are complementary.
- **Between them, an open challenge: routine, not trivial** --- widely occurring programming patterns that are still
  hard to reason about. Example: two loops that add and subtract the elements of an array.
  - automated: `0 <= i <= n`, then unrolling until the timeout;
  - interactive: write the loop again as a recursive `sum`, plus its lemmas --- tedious and error-prone;
  - "they're the same picture".
- **Why bother:** "the bottleneck has moved from writing code to trusting what was written".
- **Why LLMs are surprisingly good:** an effective problem representation, and they know the solution --- but
  their proofs need a trusted cross-check, and they cost per case.
- **Key ideas:** the task becomes a representation (TEQs), simplified by rewriting with a database of program
  lemmas until the proof is done. The database is the "knowing the solution" of an LLM, checked once and reused.

## Three claims

1. **Invariants are the wrong representation of loops.**
2. **Insight belongs in reusable lemmas** --- not in search, not in proofs of single programs.
3. **Reasoning must be incremental.**

Each part opens with the claims, the current one in red.

## Claim 1: invariants are the wrong representation → TEQs

- **Invariants** for the array initialization (`0 <= i <= n`, a quantified invariant, an exit lemma), against **a
  much better explanation**: i counts from 0 to n; a is set to z at all earlier i.
- That explanation **is** the trace equation system: `I = counter(0, 1, n)` and
  `A = stores(a, ⌊I⌋, ⌊consts(n, z)⌋)`, the history ⌊I⌋ connecting the two; one lemma each closes the goal.
- **Variable-modular, not state-modular:** `x_n = current(X)` where `X = trace(x_0, for ⌊K⌋, ⌊Y⌋ do x, k, y ↦ u)`.
  Horn clauses describe a loop by a relation on states, TEQs by what each variable computes. The loop is its own
  specification (sound, relatively complete), and program fragments get names.

## Claim 2: insight belongs in reusable lemmas → a database, and AI should make tools

- **Algorithmic invariant inference** rediscovers known facts on every program: the dialog ends with "it's a
  counter".
- **Array initialization, by lemmas:** every step is a lemma of the database (`counter_def`, `stores`,
  `current_stores`, …), none is written for the program.
- **Routine, not trivial --- as TEQs:** the first loop is `sums(…)`, the second subtracts the same sequence,
  linearity closes it. No auxiliary function: sums and their linearity are in the database.
- **Two obvious ways to use AI**, both per program: as the verifier (no trust), and as the proof generator
  (checked, but paid per program).
- The proof a language model generated for an AVL rotation reads like **assembler**. **The same proof, with a
  better tool:** with `grind` and the definitions, each theorem is one line (checked with Lean 4.34.1).
- **Thesis: AI should make tools** --- lemmas, engine rules, frontends, tests --- checked once and used for every
  program. The cost is paid once per concept, the trust is in a checked artifact.
- **The two threads meet:** TEQs make the knowledge explicit and modular, one lemma per loop shape --- what AI can
  write and a tool can check (LemmaCalc does it without AI).
- **How Cuvée is built:** recent features written by an AI agent under direction; the speaker's own experience.

## Claim 3: reasoning must be incremental → rewriting on TEQs

- **Incremental reasoning on TEQs:** rewriting proceeds one program fragment at a time; partial results stay
  useful, nothing has to be guessed up front. The same representation carries to nested loops, sorting,
  partitioning, merging.
- **State traces, variables that read each other** (the swap of two arrays): one trace per variable would be
  mutually recursive; one trace per strongly connected component, whose projections the lemmas see on demand. The
  argument: iteration k reads what no earlier iteration wrote.
- **State traces, nested loops:** the inner loop becomes one value of the outer update, `c + n`, so `c = m · n`.
- **Partial descriptions, binary search over a sorted array:** no closed form, but bounds suffice. One lemma names
  the whole loop, both variables together, a bisection of the interval; two forward lemmas give its bounds
  (`0 <= lo <= lower(a, n, x)`, `upper(a, n, x) <= hi <= n`) wherever the term occurs; the found case and the exit
  follow. The lemmas are general but not yet in the database (`doc/state-traces`, `bsearch_bisect.dfy`).

## Close

- **Evaluation:** a placeholder table (MaxPranq, Rapid, MonoCera, SV-COMP Arrays and Loops, the array algorithms),
  filled in once the runs with one version of Cuvée are done.
- **Questions for this community:** TEQ summaries as loop acceleration inside a CPA? TEQ normal forms as invariants
  in correctness witnesses? Shared frontends (C, SV-LIB, Boogie, Dafny) and Horn clauses as output.
- **Outlook:** the scope of TEQs (recursive procedures?), combination with traditional methods, interaction,
  inferring lemmas automatically.
- *Don't let AI verify programs. Let it build the tools that do, on a representation that makes their knowledge
  reusable.*
