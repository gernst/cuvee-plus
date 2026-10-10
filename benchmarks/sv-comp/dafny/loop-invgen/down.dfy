// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-invgen/down.dfy
// SV-COMP loop-invgen/down.yml (expected: safe), translated from the C program by hand: k counts
// up with i to an arbitrary n, then down with j from n to 0, and is positive before each decrement
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): k is a counter up and then down,
// both over the same n

method main() {
  var n: int;
  var k: int;
  var i: int;
  var j: int;
  k := 0;
  i := 0;
  n := *;
  while i < n {
    i := i + 1;
    k := k + 1;
  }
  j := n;
  while j > 0 {
    assert k > 0;
    j := j - 1;
    k := k - 1;
  }
}

// remaining goals of -teq -simplify:
// none
