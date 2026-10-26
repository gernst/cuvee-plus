# Canonical forms: open points

The context keeps terms in canonical form, Shostak-style (doc/prove.md, "The context"): one order of roots, the
solutions of linear equations in the classes, `Classes.normalize` as the canonizer of `Simplify.var_` and of the facts.

- **What is substituted.** Solutions that are arithmetic over variables, inside arithmetic only. Substituted in every
  position, they changed the shapes the lemmas match (the index of a store) and lost half of Arrays.
- **The cost of canonical facts.** The facts are renormalized after every merge of classes; on the examples of
  `-teq`, `-prove` and hybrid this costs about 45 % more time than canonizing each fact once when it is assumed.
  Renormalize only the facts that mention a merged class (the uses of the classes), or keep the facts as given and
  canonize at the lookups only.
- **Rules in canonical form.** Left-hand sides whose arithmetic is not canonical (e.g. `counter(i, 1, m + 1)`) are
  matched modulo the classes; which rules no longer match is unchecked.
- **Remaining losses on SV-COMP** (cloud, 120 s, against 0.51.4): Loops with the fallback 246 against 259 true
  (nla-digbench: cohendiv, geo1, geo3, prodbin, lost with the integer counts); Loops 24 against 28 false (cohencu, ps4,
  ps5, ps6 with `_unwindbound1`); MonoCera-Min 6 against 7; SV-LIB CTranslated 146 against 147.
