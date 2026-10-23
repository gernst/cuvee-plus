// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/underapprox_1-1.dfy
// SV-COMP loop-acceleration/underapprox_1-1.yml (expected: unsafe), translated from the C program
// by hand: the unsafe variant of underapprox_1-2, which asserts that y, which is 64, is not 64
//
// findings: unsafe, not closed with the lemmas of underapprox_1-2, as expected: pow(2, 6) is 64, which the lemmas
// do not evaluate either
// note: its lemmas are part of teq.dfy now (current_trace_geometric, pow_two_mod_three) and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 6, and the assertion keeps 64,
// which y is for N == 6


method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := 0;
  y := 1;
  while x < N {
    x := x + 1;
    y := y * 2;
  }
  assert y != 64;
}

// remaining goals of -teq -simplify:
// goal 64 != pow(2, 6)
