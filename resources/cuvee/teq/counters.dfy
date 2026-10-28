// counters: the shapes of traces over a counter, phases, flags, catching up, merged cases, constants, increasing and
// bounded values; an optional module over teq.dfy (-include teq:counters); the counters themselves, their reads and
// the bounds of their iteration constraints are in teq.dfy, the counters modulo m in unsigned

// two cases whose results agree under the guard of the second one, x == c, which the simplifier has substituted
// into it, are one; the second result is a variable d, since F(c) would be compared literally
// (from copysome1-1, copysome1-2)
lemma {:rw} {:teq} trace_merge_cases_ne(x0: int, n: int, c: int, d: int, F: (int) -> int)
  requires d == F(c)
  ensures trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x != c => F(x) case x == c => d)
    == trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: F(x))

// an iteration constraint that is a negated disjunction, as the test of a break, is two of them
// (from benchmark09_conjunctive, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} invs_not_or(hs: List<int>, gs: List<int>, fs: List<int>, P: (int, int, int) -> bool,
                               Q: (int, int, int) -> bool)
  ensures invs(for hs, gs, fs check h, g, f :: !(P(h, g, f) || Q(h, g, f)))
    <==> invs(for hs, gs, fs check h, g, f :: !P(h, g, f)) && invs(for hs, gs, fs check h, g, f :: !Q(h, g, f))

lemma {:rw} {:teq} current_trace_constant<a>(x: a, y: a, i: int, c: int, n: int)
  ensures current(trace(x, for ⌊counter(i, c, n)⌋ do z, v :: y))
    == if {
      case n <= 0 => x
      case 0 < n => y
    }

// a value in two phases: the first m iterations by F, the others by G, which may depend on the iteration, i.e.,
// trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case k < m => F(x, k) case m <= k => G(x, k)); the second phase starts
// where the first ends; no fold, but introduced only by a switch at a threshold of the value (trace_threshold), since
// as a fold it would take every switch at an iteration from the lemmas that read it directly, e.g. a value that keeps
// and then adds, whose remainder current_trace_step_or_keep gives (examples/dafny/teq/counters_phase_mod.dfy)
function {:teq} phases(x0: int, m: int, n: int, F: (int, int) -> int, G: (int, int) -> int): Trace<int>

lemma {:rw} {:teq} length_phases(x0: int, m: int, n: int, F: (int, int) -> int, G: (int, int) -> int)
  requires 0 <= n
  ensures length(⌊phases(x0, m, n, F, G)⌋) == n

lemma {:rw} {:teq} earlier_phases(j: int, x0: int, m: int, n: int, F: (int, int) -> int, G: (int, int) -> int)
  ensures earlier(j, ⌊phases(x0, m, n, F, G)⌋)
    == current(phases(x0, m, j, F, G))

lemma {:rw} {:teq} prefix_phases(k: int, x0: int, m: int, n: int, F: (int, int) -> int, G: (int, int) -> int)
  ensures prefix(k, ⌊phases(x0, m, n, F, G)⌋)
    == ⌊phases(x0, m, k, F, G)⌋

// a switch at a threshold b of the value, reached after b - x0 steps by 1 and kept by steps c >= 0
// (from Mono1_1-2, mono-crafted_6, mono-crafted_11, phases_1-1, phases_1-2)
lemma {:rw} {:teq} trace_threshold(x0: int, n: int, b: int, c: int)
  requires x0 <= b && 0 <= c
  ensures trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x < b => x + 1 case b <= x => x + c)
    == phases(x0, b - x0, n, (y: int, l: int) => y + 1, (y: int, l: int) => y + c)

// the second phase starts from the end of the first, both over counters from 0, which the lemmas on traces over a
// counter take, e.g. counter_def
lemma {:rw} {:teq} current_phases(x0: int, m: int, n: int, F: (int, int) -> int, G: (int, int) -> int)
  requires 0 <= m && 0 <= n
  ensures current(phases(x0, m, n, F, G))
    == if {
      case n <= m => current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: F(x, k)))
      case m < n => current(trace(current(trace(x0, for ⌊counter(0, 1, m)⌋ do x, k :: F(x, k))),
                                  for ⌊counter(0, 1, n - m)⌋ do x, k :: G(x, k + m)))
    }

// increasing phases: an upper bound holds at all earlier values iff it holds at the last of them
lemma {:rw} {:teq} invs_phases_upper(x0: int, m: int, n: int, F: (int, int) -> int, G: (int, int) -> int, B: int)
  requires 0 <= m
  requires forall y: int, l: int :: y <= F(y, l) && y <= G(y, l)
  ensures invs(for ⌊counter(0, 1, n)⌋, ⌊phases(x0, m, n, F, G)⌋ check k, x :: x < B)
    <==> (n <= 0 || current(phases(x0, m, n - 1, F, G)) < B)

// a follower: y increases by 1 whenever it does not exceed the value x of a counter with step 1, hence y is the
// larger of its initial value and the final value of x, given that it starts at least at x
// (from benchmark05_conjunctive, the only task of SV-COMP that uses it)
lemma {:rw} {:teq} current_trace_catch_up(y0: int, x0: int, n: int)
  requires 0 <= n && x0 <= y0
  ensures current(trace(y0, for ⌊counter(0, 1, n)⌋, ⌊counter(x0, 1, n)⌋ do y, k, x :: case y <= x => y + 1 case x < y => y))
    == if {
      case x0 + n <= y0 => y0
      case y0 < x0 + n => x0 + n
    }

// a flag, initially x0, that is set to c whenever D holds, is x0 at the end iff D never held, otherwise c, of any type,
// e.g. a boolean flag
// (from standard_compare_ground; examples/dafny/algorithms/is_sorted.dfy)
lemma {:rw} {:teq} current_trace_flag<a>(x0: a, c: a, n: int, hs: List<int>, D: (int, int) -> bool)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs do f, k, h :: case D(k, h) => c case !D(k, h) => f))
    == if {
      case invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: !D(k, h)) => x0
      case !invs(for ⌊counter(0, 1, n)⌋, hs check k, h :: !D(k, h)) => c
    }

// an interval that contains the initial value and that each of the three cases maps into itself contains the
// current value, an inductive invariant; the left-hand side is the conjunction of both bounds, which binds both;
// the fourth case keeps the value where no guard holds (doc/teq.md, complete guards)
// (from benchmark51_polynomial)
lemma {:rw} {:teq} current_trace_bounded(x0: int, n: int, lo: int, hi: int, C1: (int) -> bool, C2: (int) -> bool,
                                         C3: (int) -> bool, F1: (int) -> int, F2: (int) -> int, F3: (int) -> int)
  requires lo <= x0 <= hi
    && (forall y: int :: lo <= y <= hi && C1(y) ==> lo <= F1(y) <= hi)
    && (forall y: int :: lo <= y <= hi && C2(y) ==> lo <= F2(y) <= hi)
    && (forall y: int :: lo <= y <= hi && C3(y) ==> lo <= F3(y) <= hi)
  ensures
    (lo <= current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k ::
       case C1(x) => F1(x) case C2(x) => F2(x) case C3(x) => F3(x) case !(C1(x) || C2(x) || C3(x)) => x))
     && current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k ::
       case C1(x) => F1(x) case C2(x) => F2(x) case C3(x) => F3(x) case !(C1(x) || C2(x) || C3(x)) => x)) <= hi)
      <==> true

// phases: a value that adds a where a guard holds of another variable and keeps its value otherwise, e.g. z = z + 2
// membership in a counter with a positive step d, e.g. the odd positions counter(1, 2, n) of strided stores
// (from mbpr2)
lemma {:rw} {:teq} occurs_counter_step(i: int, d: int, n: int, j: int)
  requires 0 <= n && 0 < d
  ensures occurs(j, ⌊counter(i, d, n)⌋) <==> i <= j < i + n * d && (j - i) % d == 0

// the position of a value of a counter with a positive step d among its values, e.g. for the reads of strided stores
// (general form of indexof_counter_up of teq.dfy)
lemma {:rw} {:teq} indexof_counter_step(j: int, i: int, d: int, n: int)
  requires 0 < d && i <= j < i + n * d && (j - i) % d == 0
  ensures indexof(j, ⌊counter(i, d, n)⌋)
    == ((j - i) / d)
