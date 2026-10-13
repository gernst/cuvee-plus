# Story: Trace equations for program verification

CPAchecker Workshop, October 16, 2026. The storyline of the talk. The audience knows verification, mostly the
automated side, and nothing about TEQs. The talk is structured around three claims. The numbers in brackets are
pages of `figures/CPA.pdf` used as slides.

## Opening: two worlds, and what lies between

- **Automated verification** (CPAchecker, SV-COMP, Zelkova and its billion SMT queries a day) [4]: push-button,
  scales; simpler properties; the insight is found by search.
- **Interactive verification** (KeY, Isabelle, Dafny, AWS authorization) [6]: expressive specifications; the
  insight comes from a person (invariants, auxiliary functions, lemmas).
- Their strengths are complementary; **what lies between is an open challenge** (the spectrum of the KeY talk, with AWS on
  the right).
- **Routine, not trivial**: widely occurring programming patterns that are still hard to reason about, e.g. two
  loops that add and subtract the elements of an array.
  - automated: `0 <= i <= n`, then unrolling until the timeout;
  - interactive: write the loop again as a recursive `sum`, plus its lemmas --- tedious and error-prone.
  - "They're the same picture" [26].
- Why bother: "the bottleneck has moved from writing code to trusting what was written" [7].
- Why LLMs are surprisingly good: an effective problem representation, and they know the solution [12]. That is
  the motivation for a better representation, and for knowledge that is reused.

## Three claims

1. **Invariants are the wrong representation of loops.**
2. **Insight belongs in reusable lemmas** --- not in search, not in proofs of single programs.
3. **Reasoning must be incremental.**

Each part opens with the claims, the current one in red.

## Claim 1: invariants are the wrong representation → TEQs

- The array initialization with its invariants (`0 <= i <= n`, a quantified invariant, an exit lemma) against "a much
  better explanation": *i counts from 0 to n; a is set to z at all earlier i*.
- That explanation **is** the trace equation system: `I = counter(0, 1, n)`,
  `A = stores(a, ⌊I⌋, ⌊consts(n, z)⌋)`, and one lemma each closes the goal.
- What a TEQ is, for newcomers: one trace per variable, the sequence of its values at the loop head, defined as a fold
  over the iterations; *variable-modular*, where Horn clauses are *state-modular*. The loop is its own specification:
  sound, relatively complete, generated mechanically; program fragments get names.

## Claim 2: insight belongs in reusable lemmas → a database, and AI should make tools

- Search rediscovers known facts on every program: the CEGAR dialog ends with "it's a counter" [35].
- The array initialization again, by lemmas: every step (`counter`, `stores`, `current_stores`, …) is a database
  lemma, none is written for the program.
- Routine, not trivial, as TEQs: the first loop is `sums(…)`, the second subtracts the same sequence, linearity closes it.
  No auxiliary function, no lemma for the program.
- The pipeline [41]: representation + database of lemmas + rewriting → proof. The database is the "knowing the
  solution" of an LLM, but checked once and reused.
- Two obvious ways to use AI, both per program: AI as the verifier (no trust) and AI as the proof generator (checked,
  but the cost is paid per program, and the proofs read like assembler).
- The proof a language model generated for the AVL rotation reads like assembler [61]. Redone in Lean: with `grind` and the definitions, each theorem is **one line** (checked
  with Lean 4.34.1). The insight is in the tool, not in the generated proof.
- **Thesis: AI should make tools.** AI builds lemmas, engine rules, frontends and tests; they are checked once (Lean,
  the engine, tests) and every program benefits. The cost is paid once per concept, the trust is in a checked
  artifact.
- The threads meet: TEQs make the knowledge explicit and modular, one lemma per loop shape --- exactly what AI can
  write and a tool can check (LemmaCalc does it without AI).
- How Cuvée is built: recent features written by an AI agent under direction; the speaker's own experience.

## Claim 3: reasoning must be incremental → rewriting on TEQs

- Rewriting with the database proceeds one program fragment at a time; partial results stay useful, nothing has to be guessed
  up front. The same representation carries to nested loops, sorting, partitioning, merging.
- **Variables that read each other** (the swap of two arrays): one trace per variable would be mutually recursive;
  one trace per strongly connected component, whose projections the lemmas see on demand. The argument: iteration k
  reads what no earlier iteration wrote.
- **Nested loops**: the inner loop becomes one value of the outer update, `c + n`, so `c = m · n`.
- **Partial descriptions** (binary search): no closed form, but bounds suffice --- an abstraction (`incs`: grows up to
  a bound) and a forward fact (its bound, wherever the term occurs). Open: these lemmas are still the program's own.

## Close

- Questions for this community: TEQ summaries as loop acceleration inside a CPA? TEQ normal forms as invariants in
  correctness witnesses? Shared frontends (C, SV-LIB, Boogie, Dafny) and Horn clauses as output.
- Outlook [53]: the scope of TEQs (recursive procedures?), combination with traditional methods, interaction,
  inferring lemmas automatically.
- *Don't let AI verify programs. Let it build the tools that do, on a representation that makes their knowledge
  reusable.*
