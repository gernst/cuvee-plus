# Why binary search is not yet verified with `-teq -simplify`

Two versions of the same search are in this directory:

- [binary_search.dfy](binary_search.dfy) computes the probe at the top of the
  body, `mid := (lo + hi) / 2`, so `mid` is local to an iteration;
- [binary_search_solution.dfy](binary_search_solution.dfy) makes the probe a
  variable of the loop, computed before the loop and at the end of the body,
  and adds the abstractions `lows`, `highs`, `lts`, `gts`, `eqs` with their
  lemmas.

Neither is verified. Two goals remain, one for each way the loop can
terminate:

- **found**, `0 <= i`: then `i < n && a[i] == x`;
- **not found**, `!(lo < hi)` with `i < 0`: then `forall k :: 0 <= k < n ==> a[k] != x`.

`-teq -simplify` leaves a single goal whose conclusion is the disjunction of
these exits; `-split` separates them, and a second `-simplify` splits them
further into the cases of whether some probe was below, above, or equal to
`x` (14 cases for the second version).

## The trace equations

In the first version, `Lo` and `Hi` depend on each other. Each update reads
the probe `(lo + hi) / 2`, which mentions both:

```
Lo == trace(0, for ⌊K⌋, ⌊Hi⌋ do lo, k, hi ::
        case a[(hi + lo) / 2] < x => (hi + lo) / 2 + 1  case x < a[...] => lo  case a[...] == x => lo)
Hi == trace(n, for ⌊K⌋, ⌊Lo⌋ do hi, k, lo ::
        case a[(hi + lo) / 2] < x => hi  case x < a[...] => (hi + lo) / 2  case a[...] == x => hi)
```

No lemma applies, because the probe depends on the accumulator. Neither
trace can be expressed by the other one's dependency alone.

In the second version, `Lo`, `Hi`, and `I` read the probe only through the
dependency `⌊Mid⌋`. Their lemmas turn them into closed forms over the
sequence of probes:

```
Lo == lows(0, ⌊Mid⌋, lts(a, ⌊Mid⌋, x))
Hi == highs(n, ⌊Mid⌋, gts(a, ⌊Mid⌋, x))
I  == highs(-1, ⌊Mid⌋, eqs(a, ⌊Mid⌋, x))
```

The mutual dependency is moved into `Mid`. Symbolic execution substitutes the
updates of `lo` and `hi` into `mid := (lo + hi) / 2`:

```
Mid == trace(n / 2, for ⌊K⌋, ⌊Lo⌋, ⌊Hi⌋ do mid, k, lo, hi ::
         case a[mid] < x => (hi + mid + 1) / 2
         case x < a[mid] => (lo + mid) / 2
         case x == a[mid] => (hi + lo) / 2)
```

## What works now

- The found case, `a[i] == x`, is closed by the lemmas on `eqs`.
- Since higher-order patterns (version 0.26.0), `Mid` matches a lemma that
  abstracts the guards and the results over the accumulator, when it is added
  to the solution:

  ```
  trace(m0, for ⌊K⌋, ls, hs do y, k, l, h :: case B(y) => V(y, h) case C(y) => W(l, y) case D(y) => U(l, h))
    == mids(m0, ⌊K⌋, ls, hs, B, C, D, V, W, U)
  ```

  The match is `B = mid => a[mid] < x`, ..., `V = (mid, hi) => (hi + mid + 1) / 2`, ...,
  `ls = ⌊Lo⌋`, `hs = ⌊Hi⌋`. The same goals remain, since `mids` has no
  lemmas.

## What remains

In the second version, `a[i] == x` of the found exit is closed by the lemmas
on `eqs`. What remains, by exit and by the cases of the probes, is:

| exit | case conclusions | needs |
| ---- | ---------------- | ----- |
| found | `i < n` | the probe at which `x` is found is below `n` |
| not found | `lastlt + 1 < hi` | `lastlt < k` and `k < lastgt` for the `k` with `a[k] == x` |
| not found | `lastlt + 1 < n` (no probe above `x`) | `lastlt < k`, and `k < n` from the hypothesis |
| not found | `0 < hi` (no probe below `x`) | `k < lastgt`, and `0 <= k` from the hypothesis |

Here `lastlt` is `earlier(indexof(true, lts(a, ⌊Mid⌋, x)), ⌊Mid⌋)`, the last
probe that moved `lo`, and `lastgt` likewise with `gts`, the last probe that
moved `hi`. `lo` is `lastlt + 1`, or `0` if no probe was below `x`, and `hi`
is `lastgt`, or `n` if no probe was above `x`. In the first version, the goals
are the same properties, stated about the unrewritten traces.

The two exits need different things:

- **Not found** needs only sortedness and the index `k` of `x` in the
  hypothesis. `a[lastlt] < x == a[k]` gives `lastlt < k`, and
  `a[k] == x < a[lastgt]` gives `k < lastgt`, so `lo <= k < hi`, which
  contradicts the exit `hi <= lo`. This holds for any sequence of probes,
  wherever they lie.
- **Found** needs a bound on the probes. The array is a total map, so `x` may
  also occur beyond `n`, and `i < n` holds only because each probe lies below
  the `hi` of its iteration, which is at most `n`. Only the choice
  `mid == (lo + hi) / 2` of the program guarantees that.

## Why

1. **Facts about terms of the goal are never derived.** The not-found cases
   follow from `lastlt < k` and `k < lastgt`, atoms that do not occur in the
   goal, since `k` occurs only in a hypothesis. The rewriter only rewrites the
   goal; it never adds facts to the context. The lemmas on `sorted` in the
   solution are accepted but do not fire, and the lemma
   `a[lastlt] < x`, which teq.dfy has as a rewrite rule, fires only if that
   atom occurs in the goal.

2. **The relation between the probe and the bounds is lost.** The program
   keeps `mid == (lo + hi) / 2` at the loop head. The traces state it only
   implicitly: each case of `Mid` is `(lo' + hi') / 2` for the updated values,
   e.g. `(mid + 1 + hi) / 2` with `lo' = mid + 1`. Every bound on the probes
   follows from this relation together with `lo < hi`, which `invs` keeps:
   `lo <= mid < hi`. A pattern cannot recover the relation from the cases,
   since `G(UL(l, y), UH(h, y))` applies variables to non-variables and is
   outside the higher-order fragment that `Rewrite` matches. `mids` therefore
   stays opaque.

3. **The bounds of the probes need induction over the iterations.** Even with
   `lo <= mid < hi` in each iteration, `mid < n` follows only by induction:
   `hi` starts at `n` and only moves down to earlier probes, each of which is
   below the `hi` of its iteration. No lemma states this for `highs` and
   `lows`. Such a lemma would have a condition, the `invs` relating the
   probes and the bounds, whose variables do not all occur in its left-hand
   side, which `Rule.check` rejects.

4. **The probe is chosen by the program, not the abstraction.** `lows` and
   `highs` hold for any choice of probes, which is why they apply. The found
   exit depends on the choice, since the midpoint lies strictly inside the
   interval. That information is only in `Mid`, see 2.

## Paths to a proof

The arithmetic is not the problem. The context keeps difference constraints
(`Diffs` in [Theory.scala](../../../src/cuvee/simplify/Theory.scala)),
`x - y <= c` over arbitrary non-arithmetic atoms, closed under shortest paths,
where a negative cycle makes the context inconsistent. All comparisons above
have this form, e.g. `lastlt + 1 <= k`, `k + 1 <= lastgt`, and the exit
`lastgt <= lastlt + 1`, which form a negative cycle. What is missing is
getting such facts into the context (see [forward.md](../../../forward.md)).

**Not found: facts about terms, and one generic rule for sortedness.**

1. When a term `earlier(indexof(true, lts(a, ms, x)), ms)` occurs, assume
   `a[that term] < x` (and likewise for `gts`), if `occurs(true, lts(...))`
   holds. This is the existing lemma of teq.dfy, used as a fact about a term
   that occurs instead of as a rewrite rule; all its variables occur in the
   term.
2. With `a[k] == x` among the hypotheses, `a[lastlt] < x` is
   `a[lastlt] < a[k]`. This needs `x` and `a[k]` to be interchangeable via the
   equations of the context (`Chains`), which is to be checked.
3. A forward rule for sortedness, independent of `-teq`:
   `if sorted(a) && a[i] < a[j] then i < j`, triggered by the fact
   `a[i] < a[j]`, which binds both `i` and `j`.
4. `Diffs` derives the contradiction.

No search for witnesses and no saturation is needed, only facts about terms
that occur, and rules whose variables are bound by their trigger.

A smaller step, without forward rules, is a rewrite rule whose condition binds
`k` by matching `a[k] == x` against a hypothesis, with the goal's comparison
`lastlt + 1 < lastgt` as its left-hand side, and one rule for each case of the
table. It closes the not-found exit, but the lemmas are tailored to the shape
of the goal.

**Found: derived variables, and the bounds of the probes.** A variable that is
assigned last in the body by `x := e`, where `e` reads other variables of the
loop only, and that is assigned the same `e` before the loop, is a function of
the state. `-teq` could emit `Mid == maps(for Lo, Hi yield lo, hi :: (lo + hi) / 2)`
over the full traces instead of the trace with cases. `lows` and `highs`
still apply, since `⌊Mid⌋` remains a dependency, and the lemmas on `earlier`
and `maps` give `probe_j == (lo_j + hi_j) / 2`, hence `lo <= mid < hi` with
`invs(lo < hi)`. The bound `hi <= n` needs the induction of 3, as a fact about
`highs` that is assumed when its terms occur. `Diffs` then chains
`i < hi <= n`.

**An alternative abstraction: partition points instead of comparisons per
probe.** On the sorted segment `a[0..n)`, let `p` be the number of elements
below `x` and `q` the number up to `x`, e.g. `p` is
`count(true, maps(for ⌊counter(0, 1, n)⌋ yield k :: a[k] < x))`, and
`0 <= p <= q <= n`. For `0 <= m < n`, sortedness gives `a[m] < x ⟺ m < p`,
`x < a[m] ⟺ q <= m`, and `a[m] == x ⟺ p <= m < q`, as rewrite rules on the
reads of the array. The hypothesis `a[k] == x` becomes `p <= k < q`, the
guards become `mid < p`, `q <= mid`, and `p <= mid < q`, and the exits become
difference constraints: not found is `lo <= p <= k < q <= hi <= lo`, found is
`p <= i < q <= n`, so `i < n` needs no separate bound. Sortedness is used once,
where reads become indices, instead of between pairs of reads. The cost:

- the rewriting of the guards needs the probes within `[0, n)`, since the
  equivalences fail outside of the segment, i.e. the derived variable `Mid`
  again, but once, for the guards;
- the rules mention `n`, which `a[m] < x` does not, so sortedness must be
  bounded, `sorted(a, n)` as in the first version, and `n` is found in the
  context; sortedness of the whole array, as in the solution, does not
  guarantee that partition points exist;
- `lo <= p` and `q <= hi` must again be facts in the context.

## To reproduce

```
cuvee -teq examples/dafny/teq/binary_search.dfy                        # the trace equations
cuvee -teq -simplify -split -simplify examples/dafny/teq/binary_search.dfy
cuvee -teq -simplify -split -simplify examples/dafny/teq/binary_search_solution.dfy
```
