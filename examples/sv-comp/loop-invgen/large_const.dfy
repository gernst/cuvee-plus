// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-invgen/large_const.dfy
// SV-COMP ReachSafety-Loops/loop-invgen/large_const.yml (expected: safe), translated from the C program by hand: k
// grows by one of the constants 4000, 2000, 10000 in each of n < 10 iterations, chosen by an arbitrary v, then
// counts down n times and stays positive; the original assumes n < 2 in the loop, kept here, and returns otherwise,
// which the translation ends the program with by assume false
//
// findings: k increases by one of three positive constants in each iteration, chosen by v; the lemma states that a
// value that increases by a positive constant in each of its three cases exceeds its initial value after at least
// one iteration; the second loop runs n < 2 times, i.e., once; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var c1: int;
  var c2: int;
  var c3: int;
  var n: int;
  var v: int;
  var i: int;
  var k: int;
  var j: int;
  c1 := 4000;
  c2 := 2000;
  c3 := 10000;
  havoc n;
  assume 0 <= n < 10;
  k := 0;
  i := 0;
  while i < n {
    i := i + 1;
    havoc v;
    assume 0 <= v && n < 2;
    if v == 0 {
      k := k + c1;
    } else if v == 1 {
      k := k + c2;
    } else {
      k := k + c3;
    }
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
