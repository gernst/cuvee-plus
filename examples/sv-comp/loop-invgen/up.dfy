// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/up.dfy
// SV-COMP ReachSafety-Loops/loop-invgen/up.yml (expected: safe), translated from the C program by hand: k counts up
// with i to an arbitrary n, then down while j counts up from 0 to n, and is positive before each decrement
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var n: int;
  var i: int;
  var k: int;
  var j: int;
  i := 0;
  k := 0;
  havoc n;
  while i < n {
    i := i + 1;
    k := k + 1;
  }
  j := 0;
  while j < n {
    assert k > 0;
    j := j + 1;
    k := k - 1;
  }
}

// remaining goals of -teq -simplify:
// none
