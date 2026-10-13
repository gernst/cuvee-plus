// ./Cuvee.sh -teq -include teq:aggregation -prove examples/dafny/algorithms/max_element.dfy
// the maximum of a[0..n), n > 0
//
// status: verified with -teq -simplify for the postcondition that the maximum occurs among the values of a at the
// positions of a counter; the trace of m is maxs(a[0], selects(a, ⌊counter(1, 1, n')⌋)) by the lemmas of teq.dfy,
// and the bound a[k] <= m for 0 <= k < n needs the lemma below, which joins current_maxs_initial (k == 0) and
// current_maxs_earlier (1 <= k) of teq.dfy on the read a[k], since the simplifier does not split k == 0 from the rest;
// the standard postcondition exists k :: 0 <= k < n && a[k] == m is not closed: a lemma whose left-hand side is a
// quantifier is not matched, and -teq produces no witness (the position of the maximum is a trace of its own, see
// argmax.dfy); the second method keeps it as an open goal

// the maximum of the initial value a[j] and the values at the positions of a counter bounds each of them
lemma {:rw} select_le_maxs(a: array<int, int>, j: int, k: int, i: int, n: Nat)
  requires k == j || i <= k < i + integer(n)
  ensures (a[k] <= current(maxs(a[j], selects(a, ⌊counter(i, 1, n)⌋)))) <==> true

// and is attained at one of them: it occurs among the values at the positions of a counter that covers them
lemma {:rw} occurs_maxs(a: array<int, int>, j: int, i: int, n: Nat, lo: int, m: Nat)
  requires lo <= j < lo + integer(m) && lo <= i && i + integer(n) <= lo + integer(m)
  ensures occurs(current(maxs(a[j], selects(a, ⌊counter(i, 1, n)⌋))), selects(a, ⌊counter(lo, 1, m)⌋)) <==> true

method max_element(a: array<int, int>, n: int) returns (m: int)
  requires 0 < n
  ensures forall k: int :: 0 <= k < n ==> a[k] <= m
  ensures occurs(m, selects(a, ⌊counter(0, 1, natural(n))⌋))
{
  var i: int;
  m := a[0];
  i := 1;
  while i < n
  {
    if m < a[i] {
      m := a[i];
    }
    i := i + 1;
  }
}

method max_element_exists(a: array<int, int>, n: int) returns (m: int)
  requires 0 < n
  ensures forall k: int :: 0 <= k < n ==> a[k] <= m
  ensures exists k: int :: 0 <= k < n && a[k] == m
{
  var i: int;
  m := a[0];
  i := 1;
  while i < n
  {
    if m < a[i] {
      m := a[i];
    }
    i := i + 1;
  }
}
