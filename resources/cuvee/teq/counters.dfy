// counters: the shapes of traces over a counter, phases, flags, catching up, merged cases, constants, increasing and
// bounded values; an optional module over teq.dfy alone (-include teq:counters), migrated on Oct 13, 2026 from the
// module of the per-variable form (in legacy/teq.dfy): the counters themselves, their reads and the bounds of their
// iteration constraints are in teq.dfy; left in the legacy file are the rules never applied on SV-COMP, among them the
// counters modulo m of the unsigned variables of C (mods and its rules, which the C examples do not need under -prove),
// the remainders and the geometric traces, and the rules on prefixes, occurrences and indices of lists

// two cases whose results agree under the guard of the second one, x == c, which the simplifier has substituted
// into it, are one; the second result is a variable d, since F(c) would be compared literally
// (from copysome1-1, copysome1-2)
lemma {:rw} {:teq} trace_merge_cases_ne(x0: int, n: Nat, c: int, d: int, F: (int) -> int)
  requires d == F(c)
  ensures trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x != c => F(x) case x == c => d)
    == trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: F(x))

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

// an iteration constraint that is a negated disjunction, as the test of a break, is two of them
// (from benchmark09_conjunctive)
lemma {:rw} {:teq} invs_not_or(hs: List<int>, gs: List<int>, fs: List<int>, P: (int, int, int) -> bool,
                               Q: (int, int, int) -> bool)
  ensures invs(for hs, gs, fs check h, g, f :: !(P(h, g, f) || Q(h, g, f)))
    <==> invs(for hs, gs, fs check h, g, f :: !P(h, g, f)) && invs(for hs, gs, fs check h, g, f :: !Q(h, g, f))

lemma {:rw} {:teq} current_trace_constant<a>(x: a, y: a, i: int, c: int, n: Nat)
  ensures current(trace(x, for ⌊counter(i, c, n)⌋ do z, v :: y))
    == if n == zero then x else y

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

// membership in a counter with a positive step d, e.g. the odd positions counter(1, 2, n) of strided stores
// (from mbpr2; in legacy/teq.dfy from occurs_counter_step of the per-variable form)
lemma {:rw} {:teq} occurs_counter_step(i: int, d: int, n: Nat, j: int)
  requires 0 < d
  ensures occurs(j, ⌊counter(i, d, n)⌋) <==> i <= j < i + integer(n) * d && (j - i) % d == 0
