# Canonical forms: open points

The context keeps terms in canonical form, Shostak-style (doc/prove.md, "The context"): one order of roots, the
solutions of linear equations in the classes, `Classes.normalize` as the canonizer of `Simplify.var_` and of the facts.

- **What is substituted.** Only solutions that are arithmetic over variables. An alternative criterion: whether the
  right-hand side has an operator of a theory at its top (`+`, `*`, a literal, ...).
- **The cost of canonical facts.** The facts are renormalized after every merge of classes; on the examples of
  `-teq`, `-prove` and hybrid this costs about 45 % more time than canonizing each fact once when it is assumed.
  Renormalize only the facts that mention a merged class (the uses of the classes), or keep the facts as given and
  canonize at the lookups only.
- **Rules in canonical form.** Left-hand sides whose arithmetic is not canonical (e.g. `counter(i, 1, m + 1)`) are
  matched modulo the classes; which rules no longer match is unchecked.
- **Examples that became unknown** with the canonical forms: diamond.dfy, counters_phase_mod.dfy, swap.dfy (a
  timeout), one goal of hybrid/ball.dfy.
- **`-fallback` over integer counts.** Loops with the fallback lost 19 true tasks (nla-digbench: cohendiv, geo1,
  geo3, prodbin) against the naturals; the recursions now state the base case for all positions up to 0 instead of a
  conditional at each application, and a recursion whose step calls the function otherwise is generalized (it
  overflowed the stack on prodbin); to be measured. Four false `_unwindbound1` tasks (cohencu, ps4, ps5, ps6) became
  unknown in both configurations.
