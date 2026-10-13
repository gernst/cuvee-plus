# The proof of `swap.dfy` with `-teq`, formerly `-teq-state` (written for the sketch with `-simplify` on the branch `worktree-state-trace`; `-prove` follows the same steps)

The state-trace form of [examples/dafny/teq/swap.md](../teq/swap.md), from the output of `-debug rewrite` of the
verifying run (264 rewrite steps, 2.3 s, the fresh module `state.dfy`, now `resources/cuvee/teq.dfy`). The lines `view m ~> e`
are the views of markers that the matcher computed (see ideas/state-trace.md).

## The goal

```
datatype State₁₄ = State₁₄(t: int, a_: array<int, int>, b_: array<int, int>, i: int)

K == counter(0, 1, n₇)
t₁₀ == State₁₄_t(current(S))     a_₁₁ == State₁₄_a_(current(S))
b_₁₂ == State₁₄_b_(current(S))   i₁₃ == State₁₄_i(current(S))
S == trace(State₁₄(t₂, a, b, 0), for ⌊K⌋ do s, k ::
       State₁₄(State₁₄_a_(s)[State₁₄_i(s)],
               State₁₄_a_(s)[State₁₄_i(s) := State₁₄_b_(s)[State₁₄_i(s)]],
               State₁₄_b_(s)[State₁₄_i(s) := State₁₄_a_(s)[State₁₄_i(s)]],
               State₁₄_i(s) + 1))
invs(for ⌊K⌋, ⌊S⌋ check k, s :: State₁₄_i(s) < n)
0 <= integer(n₇)
==> !(i₁₃ < n) ==> forall k :: 0 <= k < n ==> a_₁₁[k] == b[k] && b_₁₂[k] == a[k]
```

One trace over the state, with the counter as its only dependency. (Since the closed definitions are substituted,
the goal writes the trace out in place of `S`, `State₁₄_a_(current(trace(...)))`, and only `n₇` is quantified; the
proof below is the same, with the views built over the trace term, and takes 2.2 s.) The arrays read each other inside one update,
where the old form had two traces over each other's histories. Nothing states a per-variable equation; the
projections are computed when a rule asks for them.

## Step 1: the counter is evaluated

Every read `State₁₄_i(s)` is a marker of a component whose projection reads no other component, so the simplifier
replaces it by its view in place. In a combinator over `⌊K⌋, ⌊S⌋`, the bound variable `s` is the state in
iteration `k`, `s == earlier(natural(k), ⌊S⌋)` (`Simplify.iterations`), so the view is
`earlier(natural(k), ⌊π_i(S)⌋)` with the projection `π_i(S) = trace(0, for ⌊K⌋, ⌊S⌋ do i, k, s :: i + 1)`:

```
trace(0, for ⌊K₉⌋ do i₂₄, k₂₅ :: i₂₄ + 1)         ~> counter(0, 1, n₇)      -- ⌊S⌋ dropped as unused, counter_def
earlier(natural(k₂₁), ⌊counter(0, 1, n₇)⌋)        ~> 0 + integer(natural(k₂₁)) * 1
integer(natural(k₂₁))                               ~> k₂₁                   -- 0 <= k₂₁ in the context
view State₁₄_i(s₂₂)                                 ~> k₂₁
```

After this, the update of `S` and all projections store at `k` and read at `k`; the index is no longer a
dependency to be matched, as `⌊I⌋` was in the old form.

## Step 2: the view of `b_` inside the projection of `a_`, and the cut

The fact `a_₁₁ == State₁₄_a_(current(S))` is simplified; nothing rewrites the marker itself. When the postcondition
later asks for `a_₁₁[k]`, and here already when the update of `S` is simplified, the rule `earlier_stores`,

```
earlier(j, ⌊stores(a, keys, values)⌋)[k]
  == if occurs(k, prefix(j, keys)) then earlier(indexof(k, prefix(j, keys)), values) else a[k]
```

meets the read `State₁₄_b_(s₂₂)[k₂₁]` in the update of the projection `π_a(S)`. The direct match of
`earlier(j, ⌊stores(...)⌋)` against the marker `State₁₄_b_(s₂₂)` fails, so the matcher computes its view, the
projection of `b_` with `⌊S⌋` among its dependencies, simplified:

```
trace(b, for ⌊K₉⌋, ⌊S₁₆⌋ do b_₂₈, k₂₉, s₃₀ :: b_₂₈[k₂₉ := State₁₄_a_(s₃₀)[k₂₉]])
  ~> stores(b, ⌊K₉⌋, maps(for ⌊K₉⌋, ⌊S₁₆⌋ yield k₂₉, s₃₀ :: State₁₄_a_(s₃₀)[k₂₉]))
view State₁₄_b_(s₂₂)
  ~> earlier(natural(k₂₁), ⌊stores(b, ⌊K₉⌋, maps(for ⌊K₉⌋, ⌊S₁₆⌋ yield k₂₉, s₃₀ :: State₁₄_a_(s₃₀)[k₂₉]))⌋)
```

Inside this view, the read `State₁₄_a_(s₃₀)[k₂₉]` of the other array is **not** projected: the view of `a_` is
the one being computed (`Context.projecting`), so the marker stays and the fold of `stores` keeps it as an opaque
stored value. This is where the eager projection regressed and where the mutual dependency is suspended. Now the
rule fires and its condition is decided by the counter lemmas:

```
State₁₄_b_(s₂₂)[k₂₁]
  ~> if occurs(k₂₁, prefix(natural(k₂₁), ⌊K₉⌋))
     then earlier(indexof(k₂₁, prefix(natural(k₂₁), ⌊K₉⌋)), maps(... State₁₄_a_(s₃₀)[k₂₉]))
     else b[k₂₁]
prefix(natural(k₂₁), ⌊K₉⌋)                          ~> ⌊counter(0, 1, natural(k₂₁))⌋     -- through K == counter(...)
occurs(k₂₁, ⌊counter(0, 1, natural(k₂₁))⌋)          ~> 0 <= k₂₁ < 0 + integer(natural(k₂₁))   -- i.e. k₂₁ < k₂₁, false
```

The `then` branch, and with it the marker of `a_`, is dropped: in iteration `k` the loop reads position `k` of the
other array, which no earlier iteration has written, so the read is of the initial array `b`. This is the same
argument as in the old proof; the difference is that the old proof followed the equation `B_ == stores(...)` of a
variable, and this one follows the view of a marker.

## Step 3: the projections close

With the cut, the update of `π_a(S)` reads no component of `s` any more, `⌊S⌋` is dropped, and the trace folds
into stores of reads of the initial array:

```
trace(a, for ⌊K₉⌋ do a_₂₀, k₂₁ :: a_₂₀[k₂₁ := b[k₂₁]])   ~> stores(a, ⌊K₉⌋, maps(for ⌊K₉⌋ yield k₂₁ :: b[k₂₁]))
maps(for ⌊K₉⌋ yield k₂₁ :: b[k₂₁])                       ~> selects(b, ⌊K₉⌋)
view State₁₄_a_(current(S₁₆))                             ~> current(stores(a, ⌊K₉⌋, selects(b, ⌊K₉⌋)))
view State₁₄_b_(current(S₁₆))                             ~> current(stores(b, ⌊K₉⌋, selects(a, ⌊K₉⌋)))
view State₁₄_t(current(S₁₆))                              ~> current(trace(t₂, for ⌊K₉⌋ do t₁₈, k₈ :: a[k₈]))
```

The views are closed forms over the inputs; the view of `t` is never used. The same cut also simplifies the
update of `S` itself in place, since the reads `State₁₄_a_(s₁₅)[k₈]` and `State₁₄_b_(s₁₅)[k₈]` occur there
(`s₁₅` is the accumulator of `S`): the state trace becomes

```
S == trace(State₁₄(t₂, a, b, 0), for ⌊K₉⌋ do s₁₅, k₈ ::
       State₁₄(a[k₈], State₁₄_a_(s₁₅)[k₈ := b[k₈]], State₁₄_b_(s₁₅)[k₈ := a[k₈]], k₈ + 1))
```

## Step 4: the number of iterations

```
view State₁₄_i(current(S₁₆))                   ~> integer(n₇)       -- current(counter(0, 1, n₇))
invs(for ⌊K₉⌋ check k₈ :: k₈ < n)              ~> integer(n₇) <= n  -- ⌊S⌋ dropped after step 1, 0 <= n
```

With the exit `!(i₁₃ < n)` and `i₁₃ == integer(n₇)`, the difference constraints give `integer(n₇) == n`.

## Step 5: the postcondition

`a_₁₁` is a variable with `a_₁₁ == State₁₄_a_(current(S))`; the rule `current_stores` matches `a_₁₁[k]` through
the definition and then through the view of step 3:

```
a_₁₁[k]                                  ~> if occurs(k, ⌊K₉⌋) then earlier(indexof(k, ⌊K₉⌋), selects(b, ⌊K₉⌋)) else a[k]
occurs(k, ⌊K₉⌋)                          ~> 0 <= k < 0 + integer(n₇)      -- true from 0 <= k < n
indexof(k, ⌊K₉⌋)                         ~> natural(k - 0)
earlier(natural(k), selects(b, ⌊K₉⌋))    ~> b[earlier(natural(k), ⌊K₉⌋)]
earlier(natural(k), ⌊K₉⌋)                ~> 0 + integer(natural(k)) * 1    ~> k
```

so `a_₁₁[k] == b[k]` is `true`; `b_₁₂[k] == a[k]` follows symmetrically, and the goal is dropped.

## Observations

- The lemmas are those of the old proof, unchanged: `counter_def`, `earlier_counter`, `prefix_counter`,
  `occurs_counter_up`, `indexof_counter_up`, the fold of `stores`, `earlier_stores`, `current_stores`,
  `earlier_selects`, the fold of `selects`, `invs_counter_upper_nonnegative`, plus `integer_natural` and
  `maps_identity`, which the old form did not need because the index was the dependency `⌊I⌋` itself.
- The mutual dependency is resolved without open trace variables or pins: the matcher suspends the component
  whose view it is computing, and the lemma on earlier stores drops the suspended read with its branch.
- The cost is in repetition. The views of `a_` and `b_` are computed about ten times each, once per context: each
  round of simplification changes the facts (`K == counter(...)` is rewritten, the update of `S` shrinks), and the
  memo keys the views by the context. The counter's view is computed in every combinator context, whose bound
  variables are fresh.
