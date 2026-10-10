// lemmas for the open goals of the MonoCera tests (see summary.md), injected by -include, e.g.
// ./Cuvee.sh -teq -simplify -split -simplify -include benchmarks/monocera/lemmas.dfy benchmarks/monocera/polished_tests/cuvee/sum/brs1.c
// the file is parsed on its own, without the state of the input or of teq.dfy, hence it repeats the declarations
// of teq.dfy that the lemmas need, exactly as there

// declarations of teq.dfy

datatype {:teq} {:lean} Nat = zero | succ(pred: Nat)

function {:teq} integer(n: Nat): int
{
  match n
  case zero => 0
  case succ(m) => integer(m) + 1
}

datatype {:teq} {:lean} List<a₀> = nil | cons(head: a₀, tail: List<a₀>)

datatype {:teq} Trace<a₀> = stop(last: a₀) | step(first: a₀, rest: Trace<a₀>)

function {:teq} current<a₀>(x₀: Trace<a₀>): a₀
{
  match x₀
  case stop(x) => x
  case step(_, xs) => current(xs)
}

function {:teq} butlast<a₀>(x₀: Trace<a₀>): List<a₀>
{
  match x₀
  case stop(_) => nil
  case step(x, xs) => cons(x, butlast(xs))
}

function {:teq} counter(x₀: int, x₁: int, x₂: Nat): Trace<int>
{
  match x₂
  case zero => stop(x₀)
  case succ(m) => step(x₀, counter(x₀ + x₁, x₁, m))
}

function {:teq} sum(values: List<int>): int
{
  match values
  case nil => 0
  case cons(v, vs) => v + sum(vs)
}

function {:teq} {:fold} stores<a, b>(a: array<a, b>, keys: List<a>, values: List<b>): Trace<array<a, b>>
{
  trace(a, for keys, values do b, k, v :: b[k := v])
}

// updates in place

// a loop that updates each position k once, by cases on the old value a[k], is the trace of the stores of the new
// values computed from the initial array, since a[k] is not modified before iteration k; the first case stores a
// constant, since a higher-order instance must contain a[k] (see Rewrite.abstraction); selects_counter of teq.dfy
// then reads the values back
// (from sum/conda)
lemma {:rw} trace_store_cases_def(a0: array<int, int>, n: Nat, c: int, P: (int) -> bool, G: (int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case P(a[k]) => a[k := c] case !P(a[k]) => a[k := G(a[k])])
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: if P(a0[k]) then c else G(a0[k])))

// a loop that stores at each position k a constant chosen by cases on k is the trace of the stores of these values,
// which current_stores of teq.dfy reads back
// (from sum/brs2)
lemma {:rw} trace_store_index_cases_def(a0: array<int, int>, n: Nat, c: int, d: int, P: (int) -> bool)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case P(k) => a[k := c] case !P(k) => a[k := d])
      == stores(a0, ⌊counter(0, 1, n)⌋, maps(for ⌊counter(0, 1, n)⌋ yield k :: if P(k) then c else d))

// a sum of n terms, each 0, c, or d, is at most n times the largest of them; the left-hand side is a comparison, whose
// bound e the side conditions compare, since sum_below_prefix of teq.dfy needs below_prefix among the facts
// (from sum/brs2)
lemma {:rw} sum_cases_below(n: Nat, c: int, d: int, e: int, P: (int) -> bool)
  requires 0 <= e && integer(n) * c <= e && integer(n) * d <= e
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then (if P(k) then c else d) else 0)) <= e

// a sum of n remainders k % m of the iterations k of a counter from 0, each between 0 and m - 1, is at most n (m - 1)
// (from sum/ms2)
lemma {:rw} sum_mod_below(n: Nat, m: int, e: int)
  requires 0 < m && integer(n) * (m - 1) <= e
  ensures sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then k % m else 0)) <= e

// strided stores

// a loop whose iteration k stores X at 2 k and Y at 2 k + 1 writes disjoint pairs of cells, which cover 0, ..., 2 n - 1;
// X and Y do not depend on the iteration, since variables of the rule do not capture the bound variables
// (from forall/array_doub_access_init_const)
lemma {:rw} select_current_trace_stride2(a0: array<int, int>, n: Nat, X: int, Y: int, j: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: a[2 * k := X][2 * k + 1 := Y]))[j]
      == if 0 <= j && j < 2 * integer(n) then (if j % 2 == 0 then X else Y) else a0[j]

// the same with three cases whose guards do not depend on the iteration, e.g. on MINVAL, and are exhaustive, such that
// one of the pairs is stored in all iterations
// (from forall/pr2)
lemma {:rw} select_current_trace_stride2_cases(a0: array<int, int>, n: Nat, P: bool, Q: bool, R: bool, X1: int, Y1: int, X2: int, Y2: int, X3: int, Y3: int, j: int)
  requires R == (!P && !Q)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(1, 1, n)⌋ do a, k, i :: case P => a[2 * k := X1][2 * k + 1 := Y1] case Q => a[2 * k := X2][2 * k + 1 := Y2] case R => a[2 * k := X3][2 * k + 1 := Y3]))[j]
      == if 0 <= j && j < 2 * integer(n)
         then (if j % 2 == 0 then (if P then X1 else if Q then X2 else X3) else (if P then Y1 else if Q then Y2 else Y3))
         else a0[j]

// stores ahead

// a loop whose iteration k stores F(k) at k + 1 and then G(k) at k, except in the last one, k + 1 == m, which stores
// at k only, leaves G(j) at j < n, since the iteration j writes it last; at n, there is F(n - 1) if n < m, the guards
// cover all iterations only for n <= m
// (from forall/rewnif)
lemma {:rw} select_current_trace_ahead(a0: array<int, int>, n: Nat, m: int, F: (int) -> int, G: (int) -> int, j: int)
  requires integer(n) <= m
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case k + 1 < m => a[k + 1 := F(k)][k := G(k)] case m == k + 1 => a[k := G(k)]))[j]
      == if 0 <= j && j < integer(n) then G(j)
         else if j == integer(n) && 0 < j && j < m then F(j - 1)
         else a0[j]

// the same for a loop down from s, whose iteration i stores F(i) at i - 1, if 1 <= i, and then G(i) at i: the cells
// s - n + 1, ..., s hold G, the cell below the last iteration the value stored ahead by it
// (from forall/rewnifrev, where it does not match yet, see summary.md)
lemma {:rw} select_current_trace_ahead_down(a0: array<int, int>, n: Nat, s: int, F: (int) -> int, G: (int) -> int, j: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(s, -1, n)⌋ do a, k, i :: case 1 <= i => a[i + (-1) := F(i)][i := G(i)] case i < 1 => a[i := G(i)]))[j]
      == if s - integer(n) < j && j <= s then G(j)
         else if j == s - integer(n) && 0 <= j && 0 < integer(n) then F(j + 1)
         else a0[j]

// arithmetic

// the quotient of a positive divisor c, which rounds down, is not positive exactly below c, e.g. CELLCOUNT / 2 <= 0
// contradicts 1 < CELLCOUNT
// (from forall/pr2)
lemma {:rw} div_nonpos(x: int, c: int)
  requires 0 < c
  ensures (x / c <= 0) == (x < c)

// the half of an even number as an equation without division, which the simplifier solves and substitutes, e.g.
// n == CELLCOUNT / 2 as CELLCOUNT == 2 * n, such that 2 * n <= i < CELLCOUNT is empty; a workaround, since solutions
// of arithmetic equations are inlined into polynomials only, here not n into 2 * n (see TODO.md)
// (from forall/pr2)
lemma {:rw} half_even(n: int, x: int)
  requires x % 2 == 0
  ensures (n == x / 2) == (x == 2 * n)

// sums in an array cell

// a sum kept in the cell j of an array, e.g. sum[0] of a one-element array in C, which the first iteration sets to c
// and the others increase by G(k), is c plus the sum of G over 1, ..., n - 1, as current_trace_reset_add of teq.dfy
// states for a scalar; only the cell j is written, hence it is read from the final array
// (from sum/brs1)
lemma {:rw} select_current_trace_reset_add(a0: array<int, int>, j: int, n: Nat, c: int, G: (int) -> int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case k == 0 => a[j := c] case 0 < k => a[j := a[j] + G(k)]))[j]
      == if n == zero then a0[j] else c + sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then G(k) else 0))

// the same where the other iterations keep the array, e.g. since the simplifier has reduced sum[0] + a[i] to sum[0]
// for a[i] == 0; the cell is c after the first iteration
// (from sum/ms1)
lemma {:rw} select_current_trace_reset_keep(a0: array<int, int>, j: int, n: Nat, c: int)
  ensures
    current(trace(a0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do a, k, i :: case k == 0 => a[j := c] case 0 < k => a))[j]
      == if n == zero then a0[j] else c
