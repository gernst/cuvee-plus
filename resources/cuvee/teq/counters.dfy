// counters and iteration constraints: traces that are counters or constant, the iteration constraints over counters
// (bounds, phases), flags, monotone and bounded traces, the lists of counters (prefix, occurs, indexof, distincts), and
// the generic simplifications of cases extracted from teq.dfy on Oct 11, 2026 as one of its modules, teq.dfy itself is
// unchanged; this file assumes the core declarations of teq.dfy (Nat, integer, natural, List, length, unspecified,
// Trace, current, butlast, counter, earlier, prefix, occurs, indexof, distincts, consts) and arithmetic.dfy; the
// attributes and the order of the lemmas are those of teq.dfy; the assembly of the preludes from the modules is not
// implemented yet, and the modules are not tested

// a variable that is increased by c in each iteration is a counter (example 2.3 of the paper)
lemma {:rw} {:teq} counter_def(i: int, c: int, n: Nat)
  ensures trace(i, for ⌊counter(0, 1, n)⌋ do x, k :: x + c)
    == counter(i, c, n)

// a variable that keeps its value in each iteration
lemma {:rw} {:teq} consts_def<a>(x: a, i: int, c: int, n: Nat)
  ensures trace(x, for ⌊counter(i, c, n)⌋ do y, v :: y)
    == consts(n, x)

// two cases whose results agree under the guard of the second one, x == c, which the simplifier has substituted
// into it, are one; the second result is a variable d, since F(c) would be compared literally
// (from copysome1-1, copysome1-2)
lemma {:rw} {:teq} trace_merge_cases_ne(x0: int, n: Nat, c: int, d: int, F: (int) -> int)
  requires d == F(c)
  ensures trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x != c => F(x) case x == c => d)
    == trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: F(x))

// the same with the guards in the other order
// (from brs1, brs1f, ifcomp, ms1, ms1f)
lemma {:rw} {:teq} trace_merge_cases_eq(x0: int, n: Nat, c: int, d: int, F: (int) -> int)
  requires d == F(c)
  ensures trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x == c => d case x != c => F(x))
    == trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: F(x))

lemma {:rw} {:teq} maps_const<a>(x: a, i: int, c: int, n: Nat)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: x)
    == ⌊consts(n, x)⌋

lemma {:rw} {:teq} maps_earlier<a>(n: Nat, xs: List<a>)
  ensures maps(for ⌊counter(0, 1, n)⌋ yield k :: earlier(natural(k), xs))
    == xs

lemma {:rw} {:teq} maps_counter_affine(a: int, b: int, i: int, c: int, n: Nat)
  ensures maps(for ⌊counter(i, c, n)⌋ yield v :: a + b * v)
    == ⌊counter(a + b * i, b * c, n)⌋

lemma {:rw} {:teq} invs_const(b: bool, i: int, c: int, n: Nat)
  ensures invs(for ⌊counter(i, c, n)⌋ check v :: b)
    <==> n == zero || b

lemma {:rw} {:teq} invs_counter_lower(m: int, i: int, c: int, n: Nat)
  ensures invs(for ⌊counter(i, c, n)⌋ check k :: m <= k)
    <==> n == zero || m <= i && m <= i + (integer(n) - 1) * c

// an upper bound m that is nonnegative holds for all values of the counter by 1 from 0 iff it holds for the number of
// its steps: a counter of an inner loop, whose bound is nonnegative by the precondition, where the disjunction of the
// general lemma below, with the case of no iteration, is not split in the context of a combinator
// (from examples/dafny/sorting/nested_sum.dfy)
lemma {:rw} {:teq} invs_counter_upper_nonnegative(m: int, n: Nat)
  requires 0 <= m
  ensures invs(for ⌊counter(0, 1, n)⌋ check k :: k < m)
    <==> integer(n) <= m

lemma {:rw} {:teq} invs_counter_upper(m: int, i: int, c: int, n: Nat)
  ensures invs(for ⌊counter(i, c, n)⌋ check k :: k < m)
    <==> n == zero || i < m && i + (integer(n) - 1) * c < m

// a counter by 1 or -1 avoids m if m lies outside of its range, e.g. for loops i != N
lemma {:rw} {:teq} invs_counter_ne_up(m: int, i: int, n: Nat)
  ensures invs(for ⌊counter(i, 1, n)⌋ check k :: k != m)
    <==> m < i || i + integer(n) <= m

lemma {:rw} {:teq} invs_counter_ne_down(m: int, i: int, n: Nat)
  ensures invs(for ⌊counter(i, -1, n)⌋ check k :: k != m)
    <==> i < m || m <= i - integer(n)

// the same counter is increasing for 0 < c, hence an upper bound B holds at all its values before the current one
// iff it holds at the last of them
// (from Mono1_1-2)
lemma {:rw} {:teq} invs_two_phases(x0: int, n: Nat, b: int, c: int, B: int)
  requires x0 <= b && 0 < c
  ensures
    invs(for ⌊counter(0, 1, n)⌋, ⌊trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c)⌋
         check k, x :: x < B)
      <==> (n == zero
             || (if integer(n) - 1 <= b - x0 then x0 + integer(n) - 1 else b + (integer(n) - 1 - (b - x0)) * c) < B)

// a lower bound of the values x of a counter with an arbitrary step holds in all iterations iff it holds at both
// ends, since the values are linear; for a counter as the third of three dependencies, with the bound as 0 < x + c,
// since b < x does not match k < x + n (see TODO.md)
// (from benchmark04_conjunctive, benchmark09_conjunctive)
lemma {:rw} {:teq} invs_counter_positive_last(i: int, d: int, n: Nat, c: int, hs: List<int>, gs: List<int>)
  ensures invs(for hs, gs, ⌊counter(i, d, n)⌋ check h, g, x :: 0 < x + c)
    <==> (n == zero || 0 < i + c && 0 < i + (integer(n) - 1) * d + c)

// the same for a counter as the second of three dependencies
// (from benchmark09_conjunctive)
lemma {:rw} {:teq} invs_counter_positive_middle(i: int, d: int, n: Nat, c: int, hs: List<int>, gs: List<int>)
  ensures invs(for hs, ⌊counter(i, d, n)⌋, gs check h, x, g :: 0 < x + c)
    <==> (n == zero || 0 < i + c && 0 < i + (integer(n) - 1) * d + c)

// an iteration constraint that is a negated disjunction, as the test of a break, is two of them
// (from benchmark09_conjunctive)
lemma {:rw} {:teq} invs_not_or(hs: List<int>, gs: List<int>, fs: List<int>, P: (int, int, int) -> bool,
                               Q: (int, int, int) -> bool)
  ensures invs(for hs, gs, fs check h, g, f :: !(P(h, g, f) || Q(h, g, f)))
    <==> invs(for hs, gs, fs check h, g, f :: !P(h, g, f)) && invs(for hs, gs, fs check h, g, f :: !Q(h, g, f))

// a trace of n steps has n values before its last one, hence none if and only if n is zero
// (from flag_loopdep)
lemma {:rw} {:teq} butlast_counter_nil(i: int, c: int, n: Nat)
  ensures (⌊counter(i, c, n)⌋ == nil) <==> (n == zero)

lemma {:rw} {:teq} butlast_consts_nil<a>(n: Nat, v: a)
  ensures (⌊consts(n, v)⌋ == nil) <==> (n == zero)

lemma {:rw} {:teq} current_counter(i: int, c: int, n: Nat)
  ensures current(counter(i, c, n))
    == i + integer(n) * c

lemma {:rw} {:teq} current_trace_constant<a>(x: a, y: a, i: int, c: int, n: Nat)
  ensures current(trace(x, for ⌊counter(i, c, n)⌋ do z, v :: y))
    == if n == zero then x else y

lemma {:rw} {:teq} current_consts<a>(n: Nat, x: a)
  ensures current(consts(n, x))
    == x

// a counter in two phases: by 1 up to the bound b, from an initial value up to b, then by c >= 0, which keeps it
// at least b
// (from Mono1_1-2, phases_1-1, phases_1-2)
lemma {:rw} {:teq} current_trace_two_phases(x0: int, n: Nat, b: int, c: int)
  requires x0 <= b && 0 <= c
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c))
    == if integer(n) <= b - x0 then x0 + integer(n) else b + (integer(n) - (b - x0)) * c

// a follower: y increases by 1 whenever it does not exceed the value x of a counter with step 1, hence y is the
// larger of its initial value and the final value of x, given that it starts at least at x
// (from benchmark05_conjunctive)
lemma {:rw} {:teq} current_trace_catch_up(y0: int, x0: int, n: Nat)
  requires x0 <= y0
  ensures current(trace(y0, for ⌊counter(0, 1, n)⌋, ⌊counter(x0, 1, n)⌋ do y, k, x :: case y <= x => y + 1 case x < y => y))
    == if x0 + integer(n) <= y0 then y0 else x0 + integer(n)

// a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c
// (from standard_compare_ground)
lemma {:rw} {:teq} current_trace_flag(x0: int, c: int, n: Nat, hs: List<int>, D: (int, int) -> bool)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do f, k, h :: case D(k, h) => c case !D(k, h) => f))
    == if invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: !D(k, h)) then x0 else c

// a value multiplied by c in each iteration, a geometric sequence
// (from underapprox_1-1, underapprox_1-2)
lemma {:rw} {:teq} current_trace_geometric(x0: int, c: int, n: Nat)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: c * x)) == x0 * pow(c, n)

// a value whose two increments are multiples of m keeps its remainder modulo m, a modular invariant
// (from loopv1)
lemma {:rw} {:teq} current_trace_mod(x0: int, n: Nat, a: int, b: int, m: int, hs: List<int>, C: (int) -> bool)
  requires 0 < m && a % m == 0 && b % m == 0
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: case C(h) => x + a case !C(h) => x + b)) % m
    == x0 % m

// a sum that is set to c in the first iteration and adds G(i) in the others is c plus the sum of G over 1, ..., n - 1,
// stated over the same iterations 0, ..., n - 1 with G(k) for 0 < k only, which the context of the map decides, rather
// than over a new length n - 1; a conditional on n, which the simplifier decides by the value of integer(n)
// (from brs1, brs1f, ms1, ms1f)
lemma {:rw} {:teq} current_trace_reset_add(x0: int, n: Nat, c: int, G: (int) -> int)
  ensures
    current(trace(x0, for ⌊counter(0, 1, n)⌋, ⌊counter(0, 1, n)⌋ do x, k, i :: case i == 0 => c case i != 0 => G(i) + x))
      == if n == zero then x0 else c + sum(maps(for ⌊counter(0, 1, n)⌋ yield k :: if 0 < k then G(k) else 0))

lemma {:rw} {:teq} earlier_counter(k: Nat, i: int, c: int, n: Nat)
  ensures earlier(k, ⌊counter(i, c, n)⌋)
    == i + integer(k) * c

lemma {:rw} {:teq} earlier_indexof<a>(x: a, xs: List<a>)
  requires occurs(x, xs)
  ensures earlier(indexof(x, xs), xs)
    == x

lemma {:rw} {:teq} earlier_consts<a>(k: Nat, n: Nat, x: a)
  ensures earlier(k, ⌊consts(n, x)⌋)
    == x

lemma {:rw} {:teq} earlier_prefix<a>(j: Nat, k: Nat, xs: List<a>)
  ensures earlier(j, prefix(k, xs))
    == earlier(j, xs)

lemma {:rw} {:teq} prefix_counter(k: Nat, i: int, c: int, n: Nat)
  ensures prefix(k, ⌊counter(i, c, n)⌋)
    == ⌊counter(i, c, k)⌋

// the prefix of the values of a function at a counter, with a further dependency that it does not use
// (from array_init_var_plus_ind3)
lemma {:rw} {:teq} prefix_maps_counter(k: Nat, i: int, c: int, n: Nat, ys: List<int>, F: (int) -> int)
  requires integer(k) <= integer(n)
  ensures prefix(k, maps(for ⌊counter(i, c, n)⌋, ys yield v, y :: F(v)))
    == maps(for ⌊counter(i, c, k)⌋ yield v :: F(v))

lemma {:rw} {:teq} prefix_consts<a>(k: Nat, n: Nat, x: a)
  ensures prefix(k, ⌊consts(n, x)⌋)
    == ⌊consts(k, x)⌋

lemma {:rw} {:teq} prefix_zero<a>(xs: List<a>)
  ensures prefix(zero, xs)
    == nil

lemma {:rw} {:teq} prefix_prefix<a>(j: Nat, k: Nat, xs: List<a>)
  ensures prefix(j, prefix(k, xs))
    == prefix(j, xs)

// a value at an index occurs in the sequence, e.g. a stored value, which current(stores(a, keys, values))[k] reads
// as earlier(indexof(k, keys), values) if k occurs among the keys; the indices of earlier are valid by construction
lemma {:rw} {:teq} occurs_earlier<a>(j: Nat, xs: List<a>)
  ensures occurs(earlier(j, xs), xs)

lemma {:rw} {:teq} occurs_counter_up(j: int, i: int, n: Nat)
  ensures occurs(j, ⌊counter(i, 1, n)⌋)
    <==> i <= j < i + integer(n)

lemma {:rw} {:teq} occurs_counter_down(j: int, i: int, n: Nat)
  ensures occurs(j, ⌊counter(i, -1, n)⌋)
    <==> i - integer(n) < j <= i

lemma {:rw} {:teq} occurs_consts<a>(x: a, n: Nat, y: a)
  ensures occurs(x, ⌊consts(n, y)⌋)
    <==> n != zero && x == y

lemma {:teq} occurs_prefix<a>(x: a, k: Nat, xs: List<a>)
  requires occurs(x, prefix(k, xs))
  ensures occurs(x, xs)

// j occurs among the values of a counter with a positive step d iff it is in the range and a multiple of d from the
// initial value (teq.dfy has this for the step 1)
// (from array_monotonic)
lemma {:rw} {:teq} occurs_counter_step(i: int, d: int, n: Nat, j: int)
  requires 0 < d
  ensures occurs(j, ⌊counter(i, d, n)⌋) <==> i <= j < i + integer(n) * d && (j - i) % d == 0

lemma {:rw} {:teq} indexof_counter_up(j: int, i: int, n: Nat)
  requires i <= j < i + integer(n)
  ensures indexof(j, ⌊counter(i, 1, n)⌋)
    == natural(j - i)

lemma {:rw} {:teq} indexof_counter_down(j: int, i: int, n: Nat)
  requires i - integer(n) < j <= i
  ensures indexof(j, ⌊counter(i, -1, n)⌋)
    == natural(i - j)

// the position of j among the values of a counter with a positive step d (see occurs_counter_step)
// (from array_of_struct_ptr_monotonic)
lemma {:rw} {:teq} indexof_counter_step(j: int, i: int, d: int, n: Nat)
  requires 0 < d && i <= j < i + integer(n) * d && (j - i) % d == 0
  ensures indexof(j, ⌊counter(i, d, n)⌋)
    == natural((j - i) / d)

lemma {:rw} {:teq} distincts_counter(i: int, c: int, n: Nat)
  requires c != 0
  ensures distincts(⌊counter(i, c, n)⌋)

lemma {:teq} distincts_prefix<a>(k: Nat, xs: List<a>)
  requires distincts(xs)
  ensures distincts(prefix(k, xs))

// a value that increases by a positive constant in each of its three cases exceeds its initial value after at
// least one iteration
// (from large_const)
lemma {:rw} {:teq} current_trace_increasing(x0: int, n: Nat, a: int, b: int, c: int, hs: List<int>, C: (int) -> bool,
                                            D: (int) -> bool, E: (int) -> bool)
  requires n != zero && 0 < a && 0 < b && 0 < c
  ensures x0 < current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h ::
    case C(h) => x + a case D(h) => x + b case E(h) => x + c))

// an interval that contains the initial value and that each of the three cases maps into itself contains the
// current value, an inductive invariant; the left-hand side is the conjunction of both bounds, which binds both
// (from benchmark51_polynomial)
lemma {:rw} {:teq} current_trace_bounded(x0: int, n: Nat, lo: int, hi: int, C1: (int) -> bool, C2: (int) -> bool,
                                         C3: (int) -> bool, F1: (int) -> int, F2: (int) -> int, F3: (int) -> int)
  requires lo <= x0 <= hi
    && (forall y: int :: lo <= y <= hi && C1(y) ==> lo <= F1(y) <= hi)
    && (forall y: int :: lo <= y <= hi && C2(y) ==> lo <= F2(y) <= hi)
    && (forall y: int :: lo <= y <= hi && C3(y) ==> lo <= F3(y) <= hi)
  ensures
    (lo <= current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case C1(x) => F1(x) case C2(x) => F2(x) case C3(x) => F3(x)))
       && current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case C1(x) => F1(x) case C2(x) => F2(x) case C3(x) => F3(x))) <= hi)
      <==> true
