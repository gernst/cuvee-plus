// experiment: an abstraction of bisection for -teq, independent of how the probe is chosen (not only the midpoint);
// the declarations of teq.dfy that the lemmas refer to are repeated here, since Trace exists only with -teq
//
// status: with the probe mid as a variable of the loop, Lo, Hi, and I become
//   lows(0, ⌊Mid⌋, lts(a, ⌊Mid⌋, x)), highs(n, ⌊Mid⌋, gts(a, ⌊Mid⌋, x)), highs(-1, ⌊Mid⌋, eqs(a, ⌊Mid⌋, x)),
// the mutual dependency remains in Mid only, whose update reads Lo, Hi, and itself;
// with -teq -simplify -split -simplify, 14 of 40 goals remain (a[i] == x is closed by the lemmas on the guards),
// which need bounds of the probes, 0 <= m < n, and the order of the probes that sortedness implies;
// the rules on sorted below are accepted but do not fire: the goals of the case not found are lastlt + 1 < hi
// under a[k] == x, which follows from lastlt < k and k < lastgt, atoms that do not occur in the goal,
// since k occurs only in the hypothesis (forward reasoning, i.e., adding facts to the context, would be needed)
// Mid does not match a pattern with the guards as plain booleans and nondeterministic increments
// (case 0 < i && b => y + i case 0 < j && c => y - j case d => y): its guards a[mid] < x and its results
// mention the accumulator mid, and variables of the pattern bound to dependencies must not (Rewrite.instantiate);
// it matches only if the guards are spelled out with the accumulator, case a[y] < x => (h + y + 1) / 2 ...,
// so abstracting them needs higher-order patterns, e.g. b(y) and v(y, l, h)

type Trace<a₀>
function current<a₀>(x₀: Trace<a₀>): a₀
function earlier<a₀>(x₀: int, x₁: seq<a₀>): a₀
function occurs<a>(x: a, xs: seq<a>): bool
function indexof<a>(x: a, xs: seq<a>): int

// two indices that move inwards: given the probes ms in the order of the iterations,
// and whether the probe moves the lower index (bs), the lower index moves up past the probe, m + 1,
// and otherwise the upper index moves down to the probe, m, for any scheme of choosing the probes
function lows(lo: int, ms: seq<int>, bs: seq<bool>): Trace<int>
function highs(hi: int, ms: seq<int>, bs: seq<bool>): Trace<int>

// the cases of the if-else chain on a[m] < x, x < a[m], and a[m] == x
lemma {:rw} {:free} forall lo: int, ms: seq<int>, bs: seq<bool>, cs: seq<bool>, ds: seq<bool> ::
  trace(lo, for ms, bs, cs, ds do l, m, b, c, d :: case b => m + 1 case c => l case d => l)
    == lows(lo, ms, bs)

lemma {:rw} {:free} forall hi: int, ms: seq<int>, bs: seq<bool>, cs: seq<bool>, ds: seq<bool> ::
  trace(hi, for ms, bs, cs, ds do h, m, b, c, d :: case b => h case c => m case d => h)
    == highs(hi, ms, cs)

// the current indices are the last probes that moved them, the initial ones if there is none
// (indexof is the last occurrence)
lemma {:rw} {:free} forall lo: int, ms: seq<int>, bs: seq<bool> ::
  current(lows(lo, ms, bs))
    == if occurs(true, bs) then earlier(indexof(true, bs), ms) + 1 else lo

lemma {:rw} {:free} forall hi: int, ms: seq<int>, bs: seq<bool> ::
  current(highs(hi, ms, bs))
    == if occurs(true, bs) then earlier(indexof(true, bs), ms) else hi

// the comparisons of the values of an array at the probes ms with x, the guards of the cases above
function lts(a: array<int, int>, ms: seq<int>, x: int): seq<bool>
function gts(a: array<int, int>, ms: seq<int>, x: int): seq<bool>
function eqs(a: array<int, int>, ms: seq<int>, x: int): seq<bool>

lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int ::
  maps(for ms yield m :: a[m] < x)
    == lts(a, ms, x)

lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int ::
  maps(for ms yield m :: x < a[m])
    == gts(a, ms, x)

lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int ::
  maps(for ms yield m :: x == a[m])
    == eqs(a, ms, x)

// the comparison holds at the last probe where it holds, if there is one,
// an equation is stated as an equivalence, since it would be a rule for x otherwise
lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int ::
  if occurs(true, lts(a, ms, x))
  then a[earlier(indexof(true, lts(a, ms, x)), ms)] < x

lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int ::
  if occurs(true, gts(a, ms, x))
  then x < a[earlier(indexof(true, gts(a, ms, x)), ms)]

lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int ::
  if occurs(true, eqs(a, ms, x))
  then (x == a[earlier(indexof(true, eqs(a, ms, x)), ms)]) <==> true

// sortedness, of the whole array, since the variables of the conditions of rules must occur in their left-hand sides,
// which do not mention the bound n
predicate sorted(a: array<int, int>)
{
  forall j: int, k: int :: j <= k ==> a[j] <= a[k]
}

// the order of the probes that sortedness implies: the last probe below x is before the last probe above x,
// and before and after, respectively, every index at which x occurs
lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int ::
  if sorted(a) && occurs(true, lts(a, ms, x)) && occurs(true, gts(a, ms, x))
  then earlier(indexof(true, lts(a, ms, x)), ms) < earlier(indexof(true, gts(a, ms, x)), ms)

lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int, k: int ::
  if sorted(a) && occurs(true, lts(a, ms, x)) && a[k] == x
  then earlier(indexof(true, lts(a, ms, x)), ms) < k

lemma {:rw} {:free} forall a: array<int, int>, ms: seq<int>, x: int, k: int ::
  if sorted(a) && occurs(true, gts(a, ms, x)) && a[k] == x
  then k < earlier(indexof(true, gts(a, ms, x)), ms)

// an index of x among the first n elements of a sorted array, -1 if there is none,
// where the probe mid is a variable of the loop, the midpoint of the remaining range, chosen after each step

method search(a: array<int, int>, n: int, x: int) returns (i: int)
  requires 0 <= n
  requires sorted(a)
  ensures 0 <= i ==> i < n && a[i] == x
  ensures i < 0 ==> forall k: int :: 0 <= k < n ==> a[k] != x
{
  var lo: int;
  var hi: int;
  var mid: int;
  lo := 0;
  hi := n;
  i := -1;
  mid := (lo + hi) / 2;
  while lo < hi && i < 0
  {
    if a[mid] < x {
      lo := mid + 1;
    } else if x < a[mid] {
      hi := mid;
    } else {
      i := mid;
    }
    mid := (lo + hi) / 2;
  }
}
