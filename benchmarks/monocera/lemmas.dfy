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
