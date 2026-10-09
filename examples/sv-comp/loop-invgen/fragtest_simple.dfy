// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/fragtest_simple.dfy
// SV-COMP ReachSafety-Loops/loop-invgen/fragtest_simple.yml (expected: safe), translated from the C program by
// hand: i and k count up together nondeterministically, then both count down n = i times, and k is checked to stay
// nonnegative (the first loop and pvlen do not matter)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 1000000

method main() {
  var N: int;
  var i: int;
  var pvlen: int;
  var k: int;
  var n: int;
  var j: int;
  var b: int;
  assume 0 < N;
  k := 0;
  i := 0;
  pvlen := *;
  b := *;
  while b != 0 && i <= N {
    i := i + 1;
    b := *;
  }
  if i > pvlen {
    pvlen := i;
  }
  i := 0;
  b := *;
  while b != 0 && i <= N {
    i := i + 1;
    k := k + 1;
    b := *;
  }
  j := 0;
  n := i;
  while true {
    assert k >= 0;
    k := k - 1;
    i := i - 1;
    j := j + 1;
    if j >= n {
      break;
    }
  }
}

// remaining goals of -teq -simplify:
// none
