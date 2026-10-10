// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-fpi/conda.dfy
// SV-COMP array-fpi/conda.yml (expected: safe), translated from the C program by hand: a is set
// to 1, then increased by 1 where it is 1, and sums up to 2 * N; sum[0] of the one-element array as a scalar
//
// findings: the two cases store at the same position, which a lemma joins into one store of a conditional value,
// which teq.dfy accelerates to stores of a constant; the sum reads them at a counter, which the lemma of ss1 gives
// as the stored values; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

// two cases that store at the same position, the iteration, are one store of a conditional value (see condm)
lemma {:rw} {:teq} trace_1(a0: array<int, int>, n: Nat, hs: List<int>, C: (array<int, int>, int, int) -> bool,
                           F: (array<int, int>, int, int) -> int, G: (array<int, int>, int, int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case C(a, k, h) => a[k := F(a, k, h)] case !C(a, k, h) => a[k := G(a, k, h)])
      == trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := if C(a, k, h) then F(a, k, h) else G(a, k, h)])

method main() {
  var N: int;
  var i: int;
  var a: array<int, int>;
  var sum: int;
  N := *;
  assume 0 < N;
  sum := 0;
  i := 0;
  while i < N {
    a := a[i := 1];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] == 1 {
      a := a[i := a[i] + 1];
    } else {
      a := a[i := a[i] - 1];
    }
    i := i + 1;
  }
  i := 0;
  while i < N {
    sum := sum + a[i];
    i := i + 1;
  }
  assert sum == 2 * N;
}

// remaining goals of -teq -simplify:
// none
