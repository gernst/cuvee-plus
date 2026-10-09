// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/standard_running-2.dfy
// SV-COMP array-examples/standard_running-2.yml (expected: safe), translated from the C program
// by hand: a is filled with arbitrary values, b records whether each element of a is nonnegative, as 1 or 0, and a
// flag f, initially 1, is reset if a and b disagree somewhere, which they do not
//
// findings: the loop that sets b has two cases that store at the same position, which the lemma joins into one
// store of a conditional value, which teq.dfy introduces as stores; then the reads of b decide the guards of the
// loop of the flag, which stays 1 (no output); a lemma for flags, x0 unless a condition held in some iteration, is
// not needed
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// two cases that store at the same position are one store of a conditional value, which teq.dfy introduces as
// stores; the guard of the second case must follow from the negation of the first
lemma {:rw} {:teq} trace_1(a0: array<int, int>, n: Nat, hs: List<int>, C: (int, int) -> bool, F: (int, int) -> int,
                           G: (int, int) -> int)
  ensures
    trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: case C(k, h) => a[k := F(k, h)] case !C(k, h) => a[k := G(k, h)])
      == trace(a0, for ⌊counter(0, 1, n)⌋, hs do a, k, h :: a[k := if C(k, h) then F(k, h) else G(k, h)])

method main() {
  var N: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var i: int;
  var f: int;
  var tmp: int;
  assume 0 < N;
  i := 0;
  while i < N {
    tmp := *;
    a := a[i := tmp];
    i := i + 1;
  }
  i := 0;
  while i < N {
    if a[i] >= 0 {
      b := b[i := 1];
    } else {
      b := b[i := 0];
    }
    i := i + 1;
  }
  f := 1;
  i := 0;
  while i < N {
    if a[i] >= 0 && b[i] == 0 {
      f := 0;
    }
    if a[i] < 0 && b[i] != 0 {
      f := 0;
    }
    i := i + 1;
  }
  assert f != 0;
}

// remaining goals of -teq -simplify:
// none
