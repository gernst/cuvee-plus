# Canonical forms: open points

The context keeps terms in canonical form, Shostak-style (doc/prove.md, "The context"): one order of roots, the
solutions of linear equations in the classes, `Classes.normalize` as the canonizer of `Simplify.var_` and of the facts.

- **What is substituted.** Solutions that are arithmetic over variables, inside arithmetic only. Substituted in every
  position, they changed the shapes the lemmas match (the index of a store) and lost half of Arrays.
- **The cost of canonical facts.** Only the facts that mention a root that a merge or solution changed are
  renormalized (`Classes.retired`), which still scans all facts per merge; a use list from roots to facts would avoid
  the scan.
- **Rules in canonical form.** Left-hand sides whose arithmetic is not canonical (e.g. `counter(i, 1, m + 1)`) are
  matched modulo the classes; which rules no longer match is unchecked.
- **Remaining losses on SV-COMP** (cloud, 120 s, against 0.51.4): timeouts on Loops, rewnifrev
  ([prove-next.md](prove-next.md), plan A).
