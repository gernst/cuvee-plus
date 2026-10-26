// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/merge.dfy
// the merge of two sorted ranges a[0..m) and b[0..n) into c[0..m + n), with the multiset of the elements stated by
// counts in the vocabulary of the lemma database
//
// status (Oct 14, 2026): verified with -teq -prove, both postconditions; a wrong postcondition, sorted(c, 0, m + n + 1)
// or the counts plus one, leaves a goal;
// the pointers i and j read each other through the guard n <= j || i < m && a[i] <= b[j], so they form one trace S
// of two accumulators, and the output trace C reads their histories ⌊S⌋.0 and ⌊S⌋.1; the lemmas name the merge as a
// whole by rules on the atoms of the postcondition, sorted(current(C), 0, s) and selects(current(C), ...), with the
// traces as rule variables matched against the variables of the goal and their equations as open conditions; the loop
// runs m + n times, and after at least that many steps the first m + n values of c are the merge, merged(a, m, b, n)

function sorted(a: array<int, int>, lo: int, hi: int): bool

// the merge by the loop over k == i + j with the pointers i and j, traces over each other: the guard and the stored
// values are higher-order, pinned by quantified side conditions, since a literal disjunctive guard is not matched
// the merge as a whole: the pointers i and j form one trace Sv, whose histories the trace Cv of the output reads;
// after at least m + n steps from 0, 0, the first m + n values of the output are the merge of a[0..m) and b[0..n)
// (the further steps store beyond them); the traces are rule variables, matched against the variables of the goal,
// whose equations are open conditions, so that no condition contains a trace itself
lemma {:rw} sorted_merge(a: array<int, int>, m: int, b: array<int, int>, n: int, c0: array<int, int>, nn: int, s: int,
                         Kv: Trace<int>, Sv: Trace<(int, int)>, Cv: Trace<array<int, int>>)
  requires Cv == trace(c0, for ⌊Kv⌋, ⌊Sv⌋.0, ⌊Sv⌋.1 do c, k, i, j ::
                   case n <= j || i < m && a[i] <= b[j] => c[k := a[i]]
                   case !(n <= j || i < m && a[i] <= b[j]) => c[k := b[j]])
  requires Sv == trace(0, 0, for ⌊Kv⌋ do i, j, k ::
                   case n <= j || i < m && a[i] <= b[j] => i + 1 case !(n <= j || i < m && a[i] <= b[j]) => i,
                   case n <= j || i < m && a[i] <= b[j] => j case !(n <= j || i < m && a[i] <= b[j]) => j + 1)
  requires Kv == counter(0, 1, nn)
  requires s == m + n && m + n <= nn
  requires 0 <= m && 0 <= n && sorted(a, 0, m) && sorted(b, 0, n)
  ensures sorted(current(Cv), 0, s) <==> true

function merged(a: array<int, int>, m: int, b: array<int, int>, n: int): List<int>

lemma {:rw} selects_merge(a: array<int, int>, m: int, b: array<int, int>, n: int, c0: array<int, int>, nn: int, s: int,
                          Kv: Trace<int>, Sv: Trace<(int, int)>, Cv: Trace<array<int, int>>)
  requires Cv == trace(c0, for ⌊Kv⌋, ⌊Sv⌋.0, ⌊Sv⌋.1 do c, k, i, j ::
                   case n <= j || i < m && a[i] <= b[j] => c[k := a[i]]
                   case !(n <= j || i < m && a[i] <= b[j]) => c[k := b[j]])
  requires Sv == trace(0, 0, for ⌊Kv⌋ do i, j, k ::
                   case n <= j || i < m && a[i] <= b[j] => i + 1 case !(n <= j || i < m && a[i] <= b[j]) => i,
                   case n <= j || i < m && a[i] <= b[j] => j case !(n <= j || i < m && a[i] <= b[j]) => j + 1)
  requires Kv == counter(0, 1, nn)
  requires s == m + n && m + n <= nn
  requires 0 <= m && 0 <= n
  ensures selects(current(Cv), ⌊counter(0, 1, s)⌋) == merged(a, m, b, n)

lemma {:rw} count_merged(a: array<int, int>, m: int, b: array<int, int>, n: int, x: int)
  requires 0 <= m && 0 <= n
  ensures count(x, merged(a, m, b, n))
    == count(x, selects(a, ⌊counter(0, 1, m)⌋)) + count(x, selects(b, ⌊counter(0, 1, n)⌋))

method main(a: array<int, int>, m: int, b: array<int, int>, n: int) returns (c: array<int, int>)
  requires 0 <= m && 0 <= n
  requires sorted(a, 0, m) && sorted(b, 0, n)
  ensures sorted(c, 0, m + n)
  ensures forall x: int :: count(x, selects(c, ⌊counter(0, 1, m + n)⌋))
    == count(x, selects(a, ⌊counter(0, 1, m)⌋)) + count(x, selects(b, ⌊counter(0, 1, n)⌋))
{
  var i: int;
  var j: int;
  var k: int;
  i := 0;
  j := 0;
  k := 0;
  while k < m + n
  {
    if n <= j || (i < m && a[i] <= b[j]) {
      c := c[k := a[i]];
      i := i + 1;
    } else {
      c := c[k := b[j]];
      j := j + 1;
    }
    k := k + 1;
  }
}
