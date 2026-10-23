// unsigned: the counters modulo m of the unsigned variables of C, whose arithmetic wraps around: the tests of loops
// bound them below m, such that the values do not wrap, and the remainders of their final values are the values
// themselves, or their remainders remain, e.g. for parities; an optional module over teq.dfy alone
// (-include teq:unsigned), restored on Oct 13, 2026 from the module counters.dfy of the per-variable form, from which
// the migration had dropped it, since the C examples do not need it, while 16 tasks of SV-COMP Loops do; proved in Lean
// (lean/)

// mods(i, c, m, n) is the trace i, (i + c) % m, ((i + c) % m + c) % m, ... of n steps, a counter that wraps around
// modulo m, e.g. an unsigned variable of C increased by c in each iteration, whose values are (i + k c) % m for
// 0 <= i < m; c = m - d counts down by d; folded from the trace of a variable that is increased by c modulo m in each
// iteration
// (from SV-COMP loop-acceleration/simple_1-2 without -unbounded)
function {:teq} {:fold} mods(i: int, c: int, m: int, n: Nat): Trace<int>
{
  trace(i, for ⌊counter(0, 1, n)⌋ do x, k :: (x + c) % m)
}

// an upper bound b of a counter by c modulo m holds for all its values iff it holds for the last of them without the
// remainder, since the values reach b before they could wrap around, b + c <= m; the initial value is below b,
// otherwise see the next lemma, whose disjunction is not split in the context of a combinator
// (from simple_1-2, underapprox_2-2)
lemma {:rw} {:teq} invs_mods_upper(b: int, i: int, c: int, m: int, n: Nat)
  requires 0 <= i && i < b && 0 < c && b + c <= m
  ensures invs(for ⌊mods(i, c, m, n)⌋ check x :: x < b)
    <==> i + (integer(n) - 1) * c < b

// (from simple_3-2, whose bound is a nondeterministic value; used on SV-COMP by sum_array-2-2, sum_by_3, vnew1 only)
lemma {:rw} {:teq} invs_mods_upper_cases(b: int, i: int, c: int, m: int, n: Nat)
  requires 0 <= i && i < m && 0 < c && b + c <= m
  ensures invs(for ⌊mods(i, c, m, n)⌋ check x :: x < b)
    <==> n == zero || i + (integer(n) - 1) * c < b

// a counter down by d = m - c modulo m stays positive iff its last value before the current one does without the
// remainder, if d divides the initial value, such that the values reach 0 before they could wrap around
// (from in-de62, count_up_down-1; used on SV-COMP by simple_4-2 only)
lemma {:rw} {:teq} invs_mods_down(i: int, c: int, m: int, n: Nat)
  requires 0 < i && i < m && c < m && i % (m - c) == 0
  ensures invs(for ⌊mods(i, c, m, n)⌋ check x :: 0 < x)
    <==> 0 < i - (integer(n) - 1) * (m - c)

lemma {:rw} {:teq} invs_mods_down_cases(i: int, c: int, m: int, n: Nat)
  requires 0 <= i && i < m && c < m && i % (m - c) == 0
  ensures invs(for ⌊mods(i, c, m, n)⌋ check x :: 0 < x)
    <==> n == zero || 0 < i - (integer(n) - 1) * (m - c)

// the final value of a counter modulo m that does not wrap around, otherwise its remainder (next lemma)
// (from simple_1-2)
lemma {:rw} {:teq} current_mods_up(i: int, c: int, m: int, n: Nat)
  requires 0 <= i + integer(n) * c && i + integer(n) * c < m
  ensures current(mods(i, c, m, n))
    == i + integer(n) * c

// (from even, odd, mod4, overflow_1-1, whose values wrap around)
lemma {:rw} {:teq} current_mods(i: int, c: int, m: int, n: Nat)
  requires 0 <= i && i < m
  ensures current(mods(i, c, m, n))
    == (i + integer(n) * c) % m

// the values of a counter modulo m that does not wrap around are those of the counter, e.g. for reads at them
// (from simple_array_index_value_1-1, sum_array-2-2)
lemma {:rw} {:teq} butlast_mods_up(i: int, c: int, m: int, n: Nat)
  requires 0 <= i && 0 <= c && i + (integer(n) - 1) * c < m
  ensures ⌊mods(i, c, m, n)⌋
    == ⌊counter(i, c, n)⌋

// a test of a loop on the remainder of a counter by 1, e.g. an int counter that is compared as unsigned, holds for all
// its values iff for the last one without the remainder, since the counter reaches b < m before it wraps around
// (from invert_string-3, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} invs_counter_mod_upper_zero(b: int, m: int, n: Nat)
  requires 0 < b && b < m
  ensures invs(for ⌊counter(0, 1, n)⌋ check k :: k % m < b)
    <==> integer(n) - 1 < b

// the same from i, with the disjunction for an initial value i that need not be below b
// (from sum_by_3, sum_by_3_abstracted; used on SV-COMP by sum_by_3 only)
lemma {:rw} {:teq} invs_counter_mod_upper_cases(b: int, i: int, m: int, n: Nat)
  requires 0 <= i && i < m && b < m
  ensures invs(for ⌊counter(0, 1, n)⌋ check k :: (k + i) % m < b)
    <==> n == zero || i + integer(n) - 1 < b

// the final value of a sum modulo m is the remainder of the sum, which the lemmas on sums compute
// (from sum_natnum, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} current_trace_mod_add_const(x0: int, n: Nat, m: int, c: int, hs: List<int>)
  requires 0 <= x0 && x0 < m
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: (k + x + c) % m))
    == current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: k + x + c)) % m

// the same for a value that is increased in some iterations only
// (from mono-crafted_10; used on SV-COMP by mono-crafted_10, trex03-2 only)
lemma {:rw} {:teq} current_trace_mod_add_cases(x0: int, n: Nat, m: int, hs: List<int>, C: (int) -> bool, F: (int) -> int)
  requires 0 <= x0 && x0 < m
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: case C(k) => (x + F(k)) % m case !C(k) => x))
    == current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do x, k, h :: case C(k) => x + F(k) case !C(k) => x)) % m
