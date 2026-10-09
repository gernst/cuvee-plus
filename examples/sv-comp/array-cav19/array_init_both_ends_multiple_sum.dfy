// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_init_both_ends_multiple_sum.dfy
// SV-COMP ReachSafety-Arrays/array-cav19/array_init_both_ends_multiple_sum.yml (expected: safe), translated from
// the C program by hand: a[i] = i, b[N - i - 1] = i, and the sum of a[i] - b[N - i - 1] is 0
//
// findings: b is filled from its end, at the positions c - k, whose reads teq.dfy expresses by occurs and indexof
// over the map of the positions; two lemmas about such decreasing positions, that x occurs iff 0 <= c - x < n, at
// the iteration c - x, reduce the sum to that of k - k; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
predicate occurs<a>(x: a, xs: seq<a>)
function indexof<a>(x: a, xs: seq<a>): int

// the positions c - k of a loop that fills an array from its end, in the iterations k = 0, ..., n - 1, are distinct:
// x occurs among them iff it is one of c, ..., c - n + 1, and it occurs at the iteration c - x (with a further
// dependency ys that the positions do not use)
lemma {:rw} {:teq} occurs_1(x: int, c: int, n: int, ys: seq<int>)
  ensures occurs(x, maps(for ⌊counter(0, 1, n)⌋, ys yield k, y :: c - k)) <==> 0 <= c - x < n
lemma {:rw} {:teq} indexof_1(x: int, c: int, n: int, ys: seq<int>)
  requires 0 <= c - x < n
  ensures indexof(x, maps(for ⌊counter(0, 1, n)⌋, ys yield k, y :: c - k)) == c - x

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var sum: int;
  assume 0 < N;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[N - i - 1 := i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + (a[i] - b[N - i - 1]);
    i := i + 1;
  }
  assert sum == 0;
}

// remaining goals of -teq -simplify:
// none
