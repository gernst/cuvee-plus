// ./Cuvee.sh -teq -include teq:aggregation -entry main -prove examples/dafny/algorithms/three_way_partition.dfy
// the three-way partition of a[0..n) around a value p (the Dutch national flag), with a single scan j as in Lomuto's
// partition: the elements below p are moved to [0, lt), those equal to p to [lt, eq), the rest stays in [eq, j)
//
// status (Oct 16, 2026): verified with -teq -prove; a wrong postcondition, the equal region up to eq inclusive or
// perm(b, a[0 := 1]), leaves a goal; as in partition.dfy, b, eq, and lt read each other and form one trace of
// (b, eq, j, lt); the counts are summarized through the views of their components (threeway_def on the array
// component, the reads of the position in iteration k as reads of a, the counts named below and beloweq), the three
// regions of the result are rules on the atoms of the postcondition over the whole trace (threeway_lt, threeway_eq,
// threeway_gt), and the bound eq <= j is stated with n' == natural(j) (beloweq_le_natural)

function perm(a: array<int, int>, b: array<int, int>): bool

// the trace of the three-way partition: the positions es of the first element not below p and ls of the first
// element not below or equal to p are further dependencies (the counts, as in partition.dfy)
function threeway(a: array<int, int>, p: int, n: int, es: List<int>, ls: List<int>): Trace<array<int, int>>

lemma {:rw} threeway_def(a: array<int, int>, p: int, n: int, es: List<int>, js: List<int>, ls: List<int>)
  ensures trace(a, for ⌊counter(0, 1, n)⌋, es, js, ls do b, k, eq, j, lt ::
      case b[k] < p => b[k := b[eq]][eq := b[k := b[eq]][lt]][lt := b[k]]
      case b[k] == p => b[k := b[eq]][eq := b[k]]
      case p < b[k] => b)
    == threeway(a, p, n, es, ls)

// the elements at the positions k, read in iteration k, are those of a, since only positions below k are written
// before iteration k
lemma {:rw} maps_threeway_read(a: array<int, int>, p: int, n: int, es: List<int>, ls: List<int>, hs: List<int>, P: (int, int, int) -> bool)
  ensures maps(for ⌊counter(0, 1, n)⌋, ⌊threeway(a, p, n, es, ls)⌋, hs yield k, b, h :: P(b[k], k, h))
    == maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: P(a[k], k, h))

lemma {:rw} maps_threeway_read_one(a: array<int, int>, p: int, n: int, es: List<int>, ls: List<int>, P: (int, int) -> bool)
  ensures maps(for ⌊counter(0, 1, n)⌋, ⌊threeway(a, p, n, es, ls)⌋ yield k, b :: P(b[k], k))
    == maps(for ⌊counter(0, 1, n)⌋ yield k :: P(a[k], k))

// the number of elements below p among the first n, and the number of those below or equal to p, named, such that
// the facts of the goal and the side conditions of the lemmas normalize to the same term (partition.dfy); the
// second keeps the counter of the loop as a further dependency hs
function {:fold} below(a: array<int, int>, p: int, n: int): int
{
  count(true, maps(for ⌊counter(0, 1, n)⌋ yield k :: a[k] < p))
}
function {:fold} beloweq(a: array<int, int>, p: int, n: int, hs: List<int>): int
{
  count(true, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a[k] < p || a[k] == p))
}

lemma {:rw} below_nonnegative(a: array<int, int>, p: int, n: int)
  ensures 0 <= below(a, p, n)

lemma {:rw} below_le_beloweq(a: array<int, int>, p: int, n: int, hs: List<int>)
  ensures below(a, p, n) <= beloweq(a, p, n, hs)

// the regions of the result on the whole state trace of (b, eq, j, lt): below the number of elements below p, equal
// up to the number of elements at most p, above from there up to n
lemma {:rw} threeway_lt(a: array<int, int>, p: int, n: int, k: int)
  requires 0 <= k < below(a, p, n)
  ensures (current(trace(a, 0, 0, 0, for ⌊counter(0, 1, n)⌋ do b, e, j, l, kk ::
                     case b[j] < p => b[j := b[e]][e := b[j := b[e]][l]][l := b[j]]
                     case b[j] == p => b[j := b[e]][e := b[j]]
                     case p < b[j] => b,
                     case b[j] < p || b[j] == p => e + 1 case p < b[j] => e,
                     j + 1,
                     case b[j] < p => l + 1 case b[j] == p || p < b[j] => l)).0[k] < p) <==> true

lemma {:rw} threeway_eq(a: array<int, int>, p: int, n: int, k: int)
  requires below(a, p, n) <= k < beloweq(a, p, n, ⌊counter(0, 1, n)⌋)
  ensures (current(trace(a, 0, 0, 0, for ⌊counter(0, 1, n)⌋ do b, e, j, l, kk ::
                     case b[j] < p => b[j := b[e]][e := b[j := b[e]][l]][l := b[j]]
                     case b[j] == p => b[j := b[e]][e := b[j]]
                     case p < b[j] => b,
                     case b[j] < p || b[j] == p => e + 1 case p < b[j] => e,
                     j + 1,
                     case b[j] < p => l + 1 case b[j] == p || p < b[j] => l)).0[k] == p) <==> true

lemma {:rw} threeway_gt(a: array<int, int>, p: int, n: int, k: int)
  requires beloweq(a, p, n, ⌊counter(0, 1, n)⌋) <= k < n
  ensures (p < current(trace(a, 0, 0, 0, for ⌊counter(0, 1, n)⌋ do b, e, j, l, kk ::
                     case b[j] < p => b[j := b[e]][e := b[j := b[e]][l]][l := b[j]]
                     case b[j] == p => b[j := b[e]][e := b[j]]
                     case p < b[j] => b,
                     case b[j] < p || b[j] == p => e + 1 case p < b[j] => e,
                     j + 1,
                     case b[j] < p => l + 1 case b[j] == p || p < b[j] => l)).0[k]) <==> true

// the bound beloweq_le for a number of iterations n == natural(m), as -teq relates it to the final value m of the
// scan, which the arithmetic does not resolve into integer(n) == m
lemma {:rw} beloweq_le_natural(a: array<int, int>, p: int, n: int, hs: List<int>, m: int)
  requires n == m && 0 <= m
  ensures beloweq(a, p, n, hs) <= m <==> true

lemma {:rw} perm_threeway(a: array<int, int>, c: array<int, int>, p: int, n: int, es: List<int>, ls: List<int>)
  ensures perm(current(threeway(a, p, n, es, ls)), c) <==> perm(a, c)

lemma {:rw} perm_refl(a: array<int, int>)
  ensures perm(a, a) <==> true

method main(a: array<int, int>, n: int, p: int) returns (b: array<int, int>, lt: int, eq: int)
  requires 0 <= n
  ensures 0 <= lt <= eq <= n
  ensures forall k: int :: 0 <= k < lt ==> b[k] < p
  ensures forall k: int :: lt <= k < eq ==> b[k] == p
  ensures forall k: int :: eq <= k < n ==> p < b[k]
  ensures perm(b, a)
{
  var j: int;
  var t: int;
  b := a;
  lt := 0;
  eq := 0;
  j := 0;
  while j < n
  {
    if b[j] < p {
      t := b[j];
      b[j] := b[eq];
      b[eq] := b[lt];
      b[lt] := t;
      lt := lt + 1;
      eq := eq + 1;
    } else if b[j] == p {
      t := b[j];
      b[j] := b[eq];
      b[eq] := t;
      eq := eq + 1;
    }
    j := j + 1;
  }
}
