// ./Cuvee.sh -teq -simplify examples/sv-comp/array-fpi/ss2.dfy
// SV-COMP ReachSafety-Arrays/array-fpi/ss2.yml (expected: safe), translated from the C program by hand: a is set to
// 1 and summed up to N, then set to 0 plus N, the sum is increased by N * N, and added to each element, which gives
// N * (N + 2) (ss3, ss4 are variants)
//
// findings: as ssina, by the lemma for reads of stores at a counter with the same definition; closed (no output)
// (ss3, ss4 are variants)

// the declarations of teq.dfy that the lemmas refer to, since its prelude is injected after parsing
type Trace<a₀>
function counter(x₀: int, x₁: int, x₂: int): Trace<int>
function current<a₀>(x₀: Trace<a₀>): a₀
function stores<a, b>(a: array<a, b>, keys: seq<a>, values: seq<b>): Trace<array<a, b>>
function selects<a, b>(a: array<a, b>, keys: seq<a>): seq<b>

// the reads of stores at the positions of a counter, at the positions of a counter of the same length, are the stored
// values; teq.dfy states this for the same keys, which are compared literally, here ⌊K⌋ and ⌊I⌋ of two counters
// with the same definition
lemma {:rw} {:teq} selects_1(a: array<int, int>, n: int, vs: seq<int>)
  ensures selects(current(stores(a, ⌊counter(0, 1, n)⌋, vs)), ⌊counter(0, 1, n)⌋) == vs

method main() {
  var N: int;
  var i: int;
  var sum: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N <= 536870911;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := 0];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  i := 0;
  while i < N {
    a := a[i := a[i] + sum];
    i := i + 1;
  }
  i := 0;
  while i < N {
    assert a[i] == N * (N + 2);
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
