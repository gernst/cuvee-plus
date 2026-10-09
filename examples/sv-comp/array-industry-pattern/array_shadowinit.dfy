// ./Cuvee.sh -teq -simplify examples/sv-comp/array-industry-pattern/array_shadowinit.dfy
// SV-COMP array-industry-pattern/array_shadowinit.yml (expected: safe), translated from the C
// program by hand: a of arbitrary size N is initialized with its index by a second index k that shadows i
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the second index k is a counter
// like i

method main() {
  var N: int;
  var a: array<int, int>;
  var i: int;
  var k: int;
  N := *;
  if N > 0 {
    i := 0;
    k := 0;
    while i < N {
      a := a[k := k];
      i := i + 1;
      k := k + 1;
    }
    i := 0;
    while i < N {
      assert a[i] == i;
      i := i + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
