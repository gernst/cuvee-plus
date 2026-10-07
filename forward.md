# Forward reasoning in the simplifier

Status: proposal, nothing is implemented. The motivating example is binary
search ([examples/dafny/teq/bsearch.md](examples/dafny/teq/bsearch.md)).

## The problem

`Simplify` and `Rewrite` reason backwards from the goal. A subterm of the goal
is rewritten when the left-hand side of a rule matches it and the rule's
condition holds in the context. The context is consulted only for decisions
(`Ctx.implied`, `Ctx.denied`, `Rewrite.holds`). New facts are never derived
from it.

Some goals hold only because of facts that the goal does not mention. In the
not-found exit of binary search, a case of the goal is

```
sorted(a) && occurs(true, lts(a, ⌊Mid⌋, x)) && occurs(true, gts(a, ⌊Mid⌋, x)) && a[k] == x && ...
  ==> lastlt + 1 < lastgt
```

where `lastlt` and `lastgt` are the last probes below and above `x`. The goal
follows from `lastlt < k` and `k < lastgt`, which sortedness gives for the
index `k` of `x`. Lemmas stating these facts exist in
[binary_search_solution.dfy](examples/dafny/teq/binary_search_solution.dfy),
but they never fire. Their conclusions are not subterms of the goal, and `k`
occurs only in a hypothesis. `Rule.check` also rejects rules whose condition
has variables that do not occur in the left-hand side.

## Matching suffices, no unification

The facts of the context are ground with respect to the lemmas. The goal's
variables (`k`, `n`, `Mid₁₄`, ...) are moved into the context by `Split` and
`Simplify` and act as constants. To apply a lemma `if P₁ && ... && Pₙ then C`:

1. match `P₁` against some fact of the context;
2. match `P₂` against some fact under the resulting substitution, and so on;
3. backtrack over the choices of facts.

This is matching, as in the instantiation of quantifiers by triggers in SMT
solvers (E-matching). `Rewrite.matches` can be reused for each premise,
including matching modulo A/C, symmetry of equations, the combinators, and
higher-order patterns.

Unification would be needed only to combine lemmas with each other, i.e.
resolution or superposition between non-ground clauses. Nothing here
requires that.

## Option A: conditions that bind variables (backward)

Variables of a condition that do not occur in the left-hand side are allowed
if they are bound by matching a condition atom against a fact of the context.
The remaining conditions, all of whose variables are bound, are decided by
`holds` as now:

```
lemma {:rw} forall a: array<int, int>, ms: seq<int>, x: int, k: int ::
  if sorted(a) && occurs(true, lts(a, ms, x)) && occurs(true, gts(a, ms, x)) && a[k] == x
  then lastlt(a, ms, x) + 1 < lastgt(a, ms, x)
```

Here `lastlt(a, ms, x)` abbreviates `earlier(indexof(true, lts(a, ms, x)), ms)`,
and `lastgt` is defined likewise with `gts`. The left-hand side is the
comparison of the goal, matched modulo moving summands. `k` is found by matching `a[k] == x` against the hypothesis.

- Changes: `Rewrite.apply` matches such conditions against the facts, which
  `Ctx` must be able to enumerate. `Rule.check` accepts variables that occur
  in a condition atom chosen for matching. Which atoms are matched could be
  marked, or follow a fixed rule, e.g. the first atom that binds the variable.
- Limitation: derived facts are not combined. The lemma must state the
  conclusion in the shape of the goal, here `+ 1 <` with both ends, instead
  of the two facts `lastlt < k` and `k < lastgt`.

## Option B: forward rules (saturation)

Lemmas with an attribute such as `{:fw}` are applied when `Ctx.assume` records
facts. Their premises are either triggers, which are matched against the
facts, or side conditions, which are decided by `holds`. Their conclusions
are simplified and assumed in turn. This allows:

- **General lemmas on sortedness.** `lastlt < k` and `k < lastgt` are derived
  separately and combined by the context. The combination needs linear
  arithmetic over the facts of the context, i.e. step 1 of the
  Fourier–Motzkin proposal in [TODO.md](TODO.md) (deciding comparisons
  against the linear facts in `Simplify.implied`). Without it,
  `lastlt < k && k < lastgt` does not give `lastlt + 1 < lastgt`.
- **Instantiation of `invs` at relevant points**, by term triggers:

  ```
  if invs(for xs check v :: P(v)) && 0 <= j < |xs| then P(earlier(j, xs))
  ```

  It is triggered by a term `earlier(j, xs)` in the goal or in the context.
  `P` is a higher-order pattern and the simplifier beta-reduces the
  conclusion. The same mechanism instantiates quantified hypotheses at the
  terms that occur, e.g. the body of `sorted`.
- **Facts by induction over the iterations**, e.g. from `invs` relating the
  probes and `hi`, and `Hi == highs(n, ...)`, that all probes are below `n`.
  For binary search this also needs the relation `mid == (lo + hi) / 2`,
  which the trace equations lose (see bsearch.md, derived variables).

Guards against blow-up:

- every variable of a conclusion is bound by the premises (the analogue of
  `Rule.check`);
- conclusions preferably over terms that occur already;
- a bound on the number of rounds and of new facts per `assume`, and at most
  one round of term triggers, since rules that keep producing new
  `earlier(...)` terms would not terminate.

This fits the existing design. `Ctx` holds the facts, the helpers of the
simplifier stay local (see CLAUDE.md), and conclusions enter as assumptions,
not as a normal form.

## Plan

1. Option A, with the lemma above in `binary_search_solution.dfy`, to check
   that it closes the not-found cases. It needs no new pass.
2. Step 1 of Fourier–Motzkin, so that the context combines linear facts.
3. Option B, starting with fact triggers (sortedness), then term triggers
   (`invs`, quantified hypotheses).
