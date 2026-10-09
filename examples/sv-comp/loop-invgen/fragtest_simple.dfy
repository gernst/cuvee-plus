// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/fragtest_simple.dfy
// SV-COMP ReachSafety-Loops/loop-invgen/fragtest_simple.yml (expected: safe), translated from the C program by
// hand: i and k count up together nondeterministically, then both count down n = i times, and k is checked to stay
// nonnegative (the first loop and pvlen do not matter)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output)

method main() {
  var i: int;
  var pvlen: int;
  var k: int;
  var n: int;
  var j: int;
  var b: int;
  k := 0;
  i := 0;
  havoc pvlen;
  havoc b;
  while b != 0 && i <= 1000000 {
    i := i + 1;
    havoc b;
  }
  if i > pvlen {
    pvlen := i;
  }
  i := 0;
  havoc b;
  while b != 0 && i <= 1000000 {
    i := i + 1;
    k := k + 1;
    havoc b;
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
