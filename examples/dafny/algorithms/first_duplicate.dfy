// ./Cuvee.sh -teq -entry main -simplify examples/dafny/algorithms/first_duplicate.dfy
// whether a[0..n) has a duplicate, with an early exit of both loops by a flag that stops them (distinct.dfy runs
// all iterations); a search in a nested loop
//
// status: verified with -teq -simplify (Oct 11, 2026, evening), with the postcondition r <==> !distincts(...) as two
// implications; the summary of the inner loop is a rewrite of the fragment r == current(R) into r == !nodup(a, k, n)
// with the trace equations, the constraints and the exit !(j < n && !r) of the early stop as side conditions
// (invs_current_duplicate); the simplifier turns the pointwise fragment of the results into a maps, so the final flag
// is r == current(results(false, ⌊K⌋, maps(for ⌊K⌋ yield k :: !nodup(a, k, n)))); the outer loop is summarized on
// the atom distincts(...) of the postcondition by one rule per case of the exit !(i < n && !r): the flag set (the
// last iteration found a duplicate) and all iterations run with the flag reset at each head (no element has a later
// duplicate); the outer counter and the flag trace are trace variables K, R of the goal with their equations as
// hypotheses, which the rules pick up as open trace variables Kv, Rv matched against these hypotheses, and the fact
// of the flags at the heads carries the counter i as an unused dependency, which the simplifier drops from a closed
// instance, so the rule takes it over an open list variable hs identified with ⌊Rv⌋ afterwards (NOTES.md); the
// postcondition as an equivalence leaves the exit in the conclusion as the disjunction i < n && !r || r == !distincts,
// which -split does not split and in whose context the rule on distincts sees neither literal: as two implications,
// each goal has its literal of the exit (r, respectively n <= i) in the context of the atom;
// the earlier attempt (NOTES.md, finding 13) closed the goal also for a wrong postcondition by a circular side
// condition, nodup_distincts, which rewrote nodup(a, k, n) to true under the hypothesis distincts(...) of the split
// goal; the rules below take the atom distincts(...) as left-hand side instead
// the inner counter (fragments.dfy)
lemma {:rw} invs_sums_counter(ks: List<int>, Ks: List<Trace<int>>, Ns: List<Nat>, Js: List<Trace<int>>, X: int -> int, c: int)
  requires invs(for ks, Ks, Ns check k, K, nn :: K == counter(0, 1, nn))
  ensures invs(for ks, Ks, Js check k, K, J :: J == sums(X(k), maps(for ⌊K⌋ yield i :: c)))
    <==> invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))

// the final value of an inner counter (fragments.dfy)
lemma {:rw} invs_current_counter(ks: List<int>, Ns: List<Nat>, Js: List<Trace<int>>, js: List<int>, X: int -> int, c: int)
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(X(k), c, nn))
  ensures invs(for ks, Js, js check k, J, j :: j == current(J))
    <==> invs(for ks, Ns, js check k, nn, j :: j == X(k) + integer(nn) * c)

// the outer trace: the initial value followed by the results of the inner loop
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>

// the outer trace: the initial value followed by the results of the inner loop
function {:fold} results<a>(x0: a, ks: List<int>, bs: List<a>): Trace<a>
{
  trace(x0, for ks, bs do x, k, b :: b)
}

// whether a[k] does not occur among a[k + 1..n)
function nodup(a: array<int, int>, k: int, n: int): bool

// the summary of the inner loop as a fragment: in iteration k, the flag r is set iff a[k] occurs among the later
// elements, given the trace equations and iteration constraints of the inner loop, which stops at the first
// duplicate or at n (the exit !(j < n && !r)), as side conditions
lemma {:rw} invs_current_duplicate(a: array<int, int>, n: int, n2: int, ks: List<int>, rs: List<bool>, Rs: List<Trace<bool>>,
                                   Js: List<Trace<int>>, Js2: List<Trace<int>>, Ns: List<Nat>, js: List<int>,
                                   Rs2: List<Trace<bool>>, rs2: List<bool>, js2: List<int>)
  requires invs(for ks, Rs, Js check k, R, J ::
    R == results(false, ⌊J⌋, maps(for ⌊J⌋ yield j :: case a[k] == a[j] => true case a[k] != a[j] => false)))
  requires invs(for ks, Ns, Js check k, nn, J :: J == counter(k + 1, 1, nn))
  requires invs(for ks, Ns, js check k, nn, j :: j == integer(nn) + k + 1)
  requires invs(for ks, Js2 check k, J :: invs(for ⌊J⌋ check j :: j < n2))
  requires Js2 == Js
  requires invs(for ks, Rs2 check k, R :: invs(for ⌊R⌋ check r :: !r))
  requires Rs2 == Rs
  requires invs(for ks, rs2, js2 check k, r, j :: !(j < n && !r))
  requires rs2 == rs && js2 == js && n2 == n
  ensures invs(for ks, rs, Rs check k, r, R :: r == current(R))
    <==> invs(for ks, rs check k, r :: r == !nodup(a, k, n))

// the results of the inner loop are a function F of the previous value and the iteration (nested_mult.dfy)
lemma {:rw} current_results_steps(x0: bool, ks: List<int>, bs: List<bool>, F: (bool, int) -> bool)
  requires invs(for ks, ⌊results(x0, ks, bs)⌋, bs check k, x, b :: b == F(x, k))
  ensures current(results(x0, ks, bs)) == current(trace(x0, for ks do x, k :: F(x, k)))

// the results of the inner loop are a function F of the iteration alone: the outer trace is the trace of F
// (current_results_steps for a summary fragment without the previous value)
lemma {:rw} current_results_const(x0: bool, ks: List<int>, bs: List<bool>, F: int -> bool)
  requires invs(for ks, bs check k, b :: b == F(k))
  ensures current(results(x0, ks, bs)) == current(trace(x0, for ks do x, k :: F(k)))

// the current value of a trace whose steps do not depend on the previous value is the last step
lemma {:rw} current_trace_last(x0: bool, m: Nat, F: int -> bool)
  ensures current(trace(x0, for ⌊counter(0, 1, m)⌋ do x, k :: F(k))) == if m == zero then x0 else F(integer(m) - 1)

// the last element has no later duplicate
lemma {:rw} nodup_last(a: array<int, int>, k: int, n: int)
  requires n <= k + 1
  ensures nodup(a, k, n) <==> true

// an element with a later duplicate contradicts distinctness: a rule on the atom with the atoms as side conditions,
// instead of a rule on nodup, which would fire inside the side condition of distincts_flags under the hypothesis
// distincts (circular, see NOTES.md)
lemma {:rw} distincts_duplicate(a: array<int, int>, k: int, n: int)
  requires !nodup(a, k, n) && 0 <= k < n
  ensures distincts(selects(a, ⌊counter(0, 1, natural(n))⌋)) <==> false

// the outer loop on the atom of the postcondition, in two rules for the two cases of the exit !(i < n && !r), which
// the goal has as a disjunction in its conclusion (the probes of fd_diag4.dfy show that the first five side conditions
// of the single rule of fd7.dfy hold and the closed disjunction n <= integer(m) || flag is not decided); with the
// postcondition as two implications, each case has its literal of the exit in the context of distincts(...):
// the flag is set: it is the result of the last iteration, which found a duplicate
lemma {:rw} distincts_flag_set(a: array<int, int>, n: int, m: Nat, flag: bool, Kv: Trace<int>)
  requires Kv == counter(0, 1, m)
  requires flag == current(results(false, ⌊Kv⌋, maps(for ⌊Kv⌋ yield k :: !nodup(a, k, n))))
  requires flag && integer(m) <= n
  ensures distincts(selects(a, ⌊counter(0, 1, natural(n))⌋)) <==> false

// all iterations ran and the flag at the head of each was reset: no element before the last has a later duplicate,
// and the last has none
lemma {:rw} distincts_flags_reset(a: array<int, int>, n: int, m: Nat, Kv: Trace<int>, Rv: Trace<bool>, hs: List<bool>,
                                  rs: List<bool>, rs2: List<bool>)
  requires Kv == counter(0, 1, m)
  requires Rv == results(false, ⌊Kv⌋, rs)
  requires invs(for ⌊Kv⌋, hs check k, h :: !h)
  requires hs == ⌊Rv⌋
  requires invs(for ⌊Kv⌋, rs2 check k, h :: h == !nodup(a, k, n))
  requires rs2 == rs
  requires n <= integer(m)
  ensures distincts(selects(a, ⌊counter(0, 1, natural(n))⌋)) <==> true

method main(a: array<int, int>, n: int) returns (r: bool)
  requires 0 <= n
  // the postcondition as two implications: the exit !(i < n && !r) of the outer loop is then a literal in the context
  // of each (as the equivalence, the goal's conclusion is i < n && !r || r == !distincts(...), where the rule on
  // distincts(...) sees neither n <= i nor r, NOTES.md)
  ensures r ==> !distincts(selects(a, ⌊counter(0, 1, natural(n))⌋))
  ensures !r ==> distincts(selects(a, ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  var j: int;
  r := false;
  i := 0;
  while i < n && !r
  {
    j := i + 1;
    while j < n && !r
    {
      if a[i] == a[j] {
        r := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
