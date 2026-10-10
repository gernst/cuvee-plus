// ./Cuvee.sh -teq -simplify examples/dafny/algorithms/three_way_partition.dfy
// the three-way partition of a[0..n) around a value p (the Dutch national flag), with a single scan j as in Lomuto's
// partition: the elements below p are moved to [0, lt), those equal to p to [lt, eq), the rest stays in [eq, j)
//
// status: verified with -teq -simplify, partition.dfy with three regions: the trace of the array is a conditional
// rotate or swap of the position k with the positions eq and lt, the numbers of elements at most p and below p so
// far (the simplifier recognizes both counts), named threeway with the counts as dependencies; the reads of the
// position k in iteration k are reads of a, since only positions below k are written before (two variants, since
// the count of eq keeps the counter of the loop as a further dependency and the count of lt does not); the counts are
// named (below, beloweq), their bounds and the three regions are rules on the atoms of the postcondition, and the
// permutation on the whole trace

function perm(a: array<int, int>, b: array<int, int>): bool

// the trace of the three-way partition: the positions es of the first element not below p and ls of the first
// element not below or equal to p are further dependencies (the counts, as in partition.dfy)
function threeway(a: array<int, int>, p: int, n: Nat, es: List<int>, ls: List<int>): Trace<array<int, int>>

lemma {:rw} threeway_def(a: array<int, int>, p: int, n: Nat, es: List<int>, js: List<int>, ls: List<int>)
  ensures trace(a, for ⌊counter(0, 1, n)⌋, es, js, ls do b, k, eq, j, lt ::
      case b[k] < p => b[k := b[eq]][eq := b[k := b[eq]][lt]][lt := b[k]]
      case b[k] == p => b[k := b[eq]][eq := b[k]]
      case p < b[k] => b)
    == threeway(a, p, n, es, ls)

// the elements at the positions k, read in iteration k, are those of a, since only positions below k are written
// before iteration k
lemma {:rw} maps_threeway_read(a: array<int, int>, p: int, n: Nat, es: List<int>, ls: List<int>, hs: List<int>, P: (int, int, int) -> bool)
  ensures maps(for ⌊counter(0, 1, n)⌋, ⌊threeway(a, p, n, es, ls)⌋, hs yield k, b, h :: P(b[k], k, h))
    == maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: P(a[k], k, h))

lemma {:rw} maps_threeway_read_one(a: array<int, int>, p: int, n: Nat, es: List<int>, ls: List<int>, P: (int, int) -> bool)
  ensures maps(for ⌊counter(0, 1, n)⌋, ⌊threeway(a, p, n, es, ls)⌋ yield k, b :: P(b[k], k))
    == maps(for ⌊counter(0, 1, n)⌋ yield k :: P(a[k], k))

// the number of elements below p among the first n, and the number of those below or equal to p, named, such that
// the facts of the goal and the side conditions of the lemmas normalize to the same term (partition.dfy); the
// second keeps the counter of the loop as a further dependency hs
function below(a: array<int, int>, p: int, n: Nat): int
function beloweq(a: array<int, int>, p: int, n: Nat, hs: List<int>): int

lemma {:rw} below_def(a: array<int, int>, p: int, n: Nat)
  ensures count(true, maps(for ⌊counter(0, 1, n)⌋ yield k :: a[k] < p)) == below(a, p, n)

lemma {:rw} beloweq_def(a: array<int, int>, p: int, n: Nat, hs: List<int>)
  ensures count(true, maps(for ⌊counter(0, 1, n)⌋, hs yield k, h :: a[k] < p || a[k] == p)) == beloweq(a, p, n, hs)

lemma {:rw} below_nonnegative(a: array<int, int>, p: int, n: Nat)
  ensures 0 <= below(a, p, n)

lemma {:rw} below_le_beloweq(a: array<int, int>, p: int, n: Nat, hs: List<int>)
  ensures below(a, p, n) <= beloweq(a, p, n, hs)

lemma {:rw} beloweq_le(a: array<int, int>, p: int, n: Nat, hs: List<int>)
  ensures beloweq(a, p, n, hs) <= integer(n)

// the result: below the number of elements below p, the elements are below p, up to the number of those below or
// equal to p, they are p, and above, they exceed p
lemma {:rw} current_threeway_below(a: array<int, int>, p: int, n: Nat, hs: List<int>, k: int)
  requires 0 <= k < below(a, p, n)
  ensures (current(threeway(a, p, n,
      ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋, hs yield k2, h :: a[k2] < p || a[k2] == p))⌋,
      ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋ yield k2 :: a[k2] < p))⌋))[k] < p)
    <==> true

lemma {:rw} current_threeway_equal(a: array<int, int>, p: int, n: Nat, hs: List<int>, k: int)
  requires below(a, p, n) <= k < beloweq(a, p, n, hs)
  ensures (current(threeway(a, p, n,
      ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋, hs yield k2, h :: a[k2] < p || a[k2] == p))⌋,
      ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋ yield k2 :: a[k2] < p))⌋))[k] == p)
    <==> true

lemma {:rw} current_threeway_above(a: array<int, int>, p: int, n: Nat, hs: List<int>, k: int)
  requires beloweq(a, p, n, hs) <= k < integer(n)
  ensures (p < current(threeway(a, p, n,
      ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋, hs yield k2, h :: a[k2] < p || a[k2] == p))⌋,
      ⌊counts(0, true, maps(for ⌊counter(0, 1, n)⌋ yield k2 :: a[k2] < p))⌋))[k])
    <==> true

lemma {:rw} perm_threeway(a: array<int, int>, c: array<int, int>, p: int, n: Nat, es: List<int>, ls: List<int>)
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
