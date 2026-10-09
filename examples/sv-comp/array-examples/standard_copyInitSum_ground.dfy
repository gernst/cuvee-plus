// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_copyInitSum_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/standard_copyInitSum_ground.yml (expected: safe), translated from the C
// program by hand: a is initialized to 42, copied into b, incr is added to each element of b, which is then 42 +
// incr
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the loops of initialization,
// copy, and increment are introduced as stores over counters, and the reads of b at x < n are resolved by occurs
// and indexof
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var incr: int;
  var i: int;
  var x: int;
  assume 0 < N;
  incr := *;
  i := 0;
  while i < N {
    a := a[i := 42];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := a[i]];
    i := i + 1;
  }
  i := 0;
  while i < N {
    b := b[i := b[i] + incr];
    i := i + 1;
  }
  x := 0;
  while x < N {
    assert b[x] == 42 + incr;
    x := x + 1;
  }
}

// remaining goals of -teq -simplify:
// none
