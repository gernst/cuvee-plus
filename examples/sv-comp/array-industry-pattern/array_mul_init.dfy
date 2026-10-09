// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/array-industry-pattern/array_mul_init.dfy
// SV-COMP ReachSafety-Arrays/array-industry-pattern/array_mul_init.yml (expected: safe), translated from the C
// program by hand: a and b are initialized to the index, then at arbitrary positions overwritten by an arbitrary k
// and its square, such that b is a or its square at all positions
//
// findings: the second loop stores k and k * k at the positions of the iterations, guarded by an arbitrary choice,
// the lemma reads such guarded stores with the values of the dependencies at the iteration of the position (see
// copysome1-1), and -split splits the conditionals; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var a: array<int, int>;
  var b: array<int, int>;
  var k: int;
  var i: int;
  var c: int;
  i := 0;
  while i < 100000 {
    a := a[i := i];
    b := b[i := i];
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    havoc c;
    if c != 0 {
      havoc k;
      assume -32768 <= k <= 32767;
      a := a[i := k];
      b := b[i := k * k];
    }
    i := i + 1;
  }
  i := 0;
  while i < 100000 {
    assert a[i] == b[i] || b[i] == a[i] * a[i];
    i := i + 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// none
