# Why `swap.dfy` verifies with `-teq -simplify`

`swap.dfy` exchanges the first `n` elements of two arrays in a loop without an
invariant:

```dafny
method swap(a: array<int, int>, b: array<int, int>, n: int) returns (a_: array<int, int>, b_: array<int, int>)
  requires 0 <= n
  ensures forall k: int :: 0 <= k < n ==> a_[k] == b[k] && b_[k] == a[k]
{
  ...
  a_ := a; b_ := b; i := 0;
  while i < n { t := a_[i]; a_[i] := b_[i]; b_[i] := t; i := i + 1; }
}
```

`cuvee -teq -simplify examples/dafny/teq/swap.dfy` prints nothing: the goal
simplifies to `true` and is dropped. No solver is involved. This note follows
the steps in the output of `-debug simplify,rewrite`.

## The trace equation system

`-teq` summarizes the loop by one trace per variable, i.e. the sequence of its
values at the loop head (`A_`, `B_`, `T`, `I`). `K` counts the iterations.
`⌊X⌋` is all but the last element of `X`, and `current(X)` is the last one:

```
K == counter(0, 1, n₇)
A_ == trace(a, for ⌊K⌋, ⌊B_⌋, ⌊I⌋ do a_₄, k₈, b_₅, i₆ :: a_₄[i₆ := b_₅[i₆]])
B_ == trace(b, for ⌊K⌋, ⌊A_⌋, ⌊I⌋ do b_₅, k₈, a_₄, i₆ :: b_₅[i₆ := a_₄[i₆]])
T  == trace(t₂, for ⌊K⌋, ⌊A_⌋, ⌊I⌋ do t₃, k₈, a_₄, i₆ :: a_₄[i₆])
I  == trace(0, for ⌊K⌋ do i₆, k₈ :: i₆ + 1)
invs(for ⌊K⌋, ... ⌊I⌋ check ..., i₆ :: i₆ < n)          // the loop test held in each iteration
a_₁₅ == current(A_), b_₁₆ == current(B_), i₁₇ == current(I), !(i₁₇ < n)
==> forall k :: 0 <= k < n ==> a_₁₅[k] == b[k] && b_₁₆[k] == a[k]
```

Symbolic execution substitutes `t := a_[i]` into the update of `b_`. So the
update of `A_` reads the previous value of `b_`, and the update of `B_` reads
the previous value of `a_`. The two traces are defined in terms of each other.
That mutual dependency is what has to be resolved, and no invariant states
how.

## Step 1: the updates are recognized as stores

The lemma

```
trace(a, for keys, values do b, k, v :: b[k := v]) == stores(a, keys, values)
```

matches both array traces. The keys are `⌊I⌋`, and the stored values become a
`maps` over all dependencies:

```
[rewrite] trace(a, for ⌊K₉⌋, ⌊B_₁₂⌋, ⌊I₁₃⌋ do a_₄, k₈, b_₅, i₆ :: a_₄[i₆ := b_₅[i₆]])
       ~> stores(a, ⌊I₁₃⌋, maps(for ⌊K₉⌋, ⌊B_₁₂⌋, ⌊I₁₃⌋ yield k₈, b_₅, i₆ :: b_₅[i₆]))
[rewrite] trace(b, for ⌊K₉⌋, ⌊A_₁₁⌋, ⌊I₁₃⌋ do b_₅, k₈, a_₄, i₆ :: b_₅[i₆ := a_₄[i₆]])
       ~> stores(b, ⌊I₁₃⌋, maps(for ⌊K₉⌋, ⌊A_₁₁⌋, ⌊I₁₃⌋ yield k₈, a_₄, i₆ :: a_₄[i₆]))
[rewrite] trace(0, for ⌊K₉⌋ do i₆, k₈ :: i₆ + 1)
       ~> counter(0, 1, n₇)
```

The dependency is still there, now inside the stored values: `A_` stores
values read from `B_`, and vice versa. The keys, however, are known: the
counter `0, 1, ..., n₇ - 1`.

## Step 2: the bound variables are the values in iteration k

Inside a combinator whose first dependency is `⌊counter(0, 1, n)⌋`,
`Simplify.iterations` assumes `0 <= k₈ < n` and binds every other variable to
its value in iteration `k₈`: `z == earlier(k₈, ⌊Z⌋)`. For the index this gives
`i₆ == k₈`:

```
[rewrite] earlier(k₈, ⌊I₁₃⌋)
       ~> 0 + k₈ * 1
[simplify] a_₄[i₆]
        ~> a_₄[k₈]
```

The array variables are bound likewise, `a_₄ == earlier(k₈, ⌊A_⌋)` and
`b_₅ == earlier(k₈, ⌊B_⌋)`. The other conjuncts are assumed as well, among them
`A_ == stores(a, ⌊I⌋, ...)` and `B_ == stores(b, ⌊I⌋, ...)`. When it matches a
lemma, the rewriter looks through such equations (`Ctx.↑`, see
`Rewrite.scala`). It therefore sees `a_₄` as
`earlier(k₈, ⌊stores(a, ⌊I⌋, ...)⌋)`.

## Step 3: the interdependence is cut (the key step)

The relevant lemma is about reading an earlier state of a stores trace at an
index that has not been written so far:

```
if !occurs(k, prefix(j, keys))
then earlier(j, ⌊stores(a, keys, values)⌋)[k] == a[k]
```

Here `j` and `k` are both the iteration `k₈`, and the keys are `⌊I⌋`. Its
condition is decided by two more lemmas. The first `k₈` keys of the counter
are `0, ..., k₈ - 1`, and `k₈` is not among them:

```
[rewrite] prefix(k₈, ⌊I₁₃⌋)
       ~> ⌊counter(0, 1, k₈)⌋
[rewrite] occurs(k₈, ⌊counter(0, 1, k₈)⌋)
       ~> 0 <= k₈ < 0 + k₈
[simplify] 0 <= k₈ < 0 + k₈
        ~> false
[simplify] !occurs(k₈, prefix(k₈, ⌊I₁₃⌋))
        ~> true
[rewrite] a_₄[k₈]
       ~> a[k₈]
```

In the trace of `t`, and in the values stored into `B_`, the read `a_₄[k₈]` of
the current array becomes `a[k₈]`, a read of the **initial** array. In the
same way, `b_₅[k₈]` in the values stored into `A_` becomes `b[k₈]`:

```
[rewrite] b_₅[k₈]
       ~> b[k₈]
```

The lemma only needs the keys of the other trace, never its stored values.
Those values are exactly where the reference back to the first trace sits, so
the cycle is never followed. The reason is plain: in iteration `k`, the loop
has written only the indices `0, ..., k - 1`. Element `k` of both arrays still
has its initial value when the loop reads it.

Now the bodies no longer mention `a_₄` and `b_₅`. The simplifier drops the
unused dependencies `⌊A_⌋` and `⌊B_⌋`, and then `⌊I⌋`, so each `maps` becomes
a plain read of the initial array:

```
[rewrite] maps(for ⌊K₉⌋, ⌊I₁₃⌋ yield k₈, i₆ :: b[k₈])
       ~> selects(b, ⌊K₉⌋)
[simplify] A_₁₁ == stores(a, ⌊I₁₃⌋, maps(for ⌊K₉⌋, ⌊B_₁₂⌋, ⌊I₁₃⌋ yield k₈, b_₅, i₆ :: b_₅[i₆]))
        ~> A_₁₁ == stores(a, ⌊I₁₃⌋, selects(b, ⌊K₉⌋))
[simplify] B_₁₂ == stores(b, ⌊I₁₃⌋, maps(for ⌊K₉⌋, ⌊A_₁₁⌋, ⌊I₁₃⌋ yield k₈, a_₄, i₆ :: a_₄[i₆]))
        ~> B_₁₂ == stores(b, ⌊I₁₃⌋, selects(a, ⌊K₉⌋))
```

The two traces are now closed forms over the inputs alone:
`A_ == stores(a, ⌊I⌋, selects(b, ⌊K⌋))` and
`B_ == stores(b, ⌊I⌋, selects(a, ⌊K⌋))`. The trace `T` of the temporary
becomes `trace(t₂, ... :: a[k₈])`, which nothing uses any more, so its
equation is dropped as well.

## Step 4: the number of iterations

The loop tests in `invs` give `n₇ <= n`. With the exit condition
`n <= i₁₇` and `i₁₇ == current(I) == n₇`, this yields `n₇ == n`. So the
counters become `counter(0, 1, n)`.

## Step 5: the postcondition

With `a_₁₅ == current(A_)`, the final read is decided by the lemma about
reading the last state of a stores trace:

```
current(stores(a, keys, values))[k] == if occurs(k, keys) then earlier(indexof(k, keys), values) else a[k]
```

```
[rewrite] a_₁₅[k]
       ~> if occurs(k, ⌊I₁₃⌋) then earlier(indexof(k, ⌊I₁₃⌋), selects(b, ⌊K₉⌋)) else a[k]
[rewrite] occurs(k, ⌊I₁₃⌋)
       ~> 0 <= k < 0 + n                 // true by the antecedent 0 <= k < n
[rewrite] indexof(k, ⌊I₁₃⌋)
       ~> k - 0
[rewrite] earlier(k, selects(b, ⌊K₉⌋))
       ~> b[earlier(k, ⌊K₉⌋)]
[rewrite] earlier(k, ⌊K₉⌋)
       ~> 0 + k * 1
[simplify] a_₁₅[k] == b[k]
        ~> true
```

`b_₁₆[k] == a[k]` follows symmetrically, so the goal is `true`.

## What makes this work

- The arrays are only updated at the loop index, and the index is a counter
  with step 1. So the keys of both `stores` traces are known, and distinct.
- Each iteration reads the other array at the index it is about to write,
  which no earlier iteration has written. The lemma for unwritten indices
  (`!occurs(k, prefix(j, keys))`) applies, and it replaces the read by one of
  the initial array without looking at the stored values. That is what removes
  the mutual dependency between `A_` and `B_`.
- If the loop read an index that an earlier iteration had written, e.g.
  `a_[i - 1]`, the other lemma (`occurs(k, prefix(j, keys))`) would apply
  instead. It returns an earlier stored value, which still refers to the
  other trace, and the dependency would not be resolved this way.

To reproduce:

```
mill -i run -teq examples/dafny/teq/swap.dfy                                # the trace equation system
mill -i run -teq -simplify -debug simplify,rewrite examples/dafny/teq/swap.dfy
```
