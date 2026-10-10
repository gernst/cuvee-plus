// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops-crafted-1/sumt2.dfy
// SV-COMP loops-crafted-1/sumt2.yml (expected: safe), translated from the C program by hand: l
// counts to n, at most SIZE == 20000001, unsigned, and i and j count the even and the odd values of l, which add up
// to l
//
// findings: i and j count the even and odd iterations, which teq.dfy introduces as counts of a map of k % 2 and of
// k % 2 == 0; lemmas count false as the others than true, the iterations where k % 2 == r as the occurrences of r,
// and the remainders (see half.dfy), which gives both counts the same closed form, since they differ in the names
// of their bound variables otherwise (see TODO.md); the lemmas keep
// the dependencies as matched; closed (no output)
// note: its lemmas are part of teq.dfy now (count_remainder, count_false_true, count_true_eq) and are removed here

method main() {
  var n: int;
  var i: int;
  var j: int;
  var l: int;
  n := *;
  assume 0 <= n;
  i := 0;
  j := 0;
  l := 0;
  while l < n {
    if l % 2 == 0 {
      i := i + 1;
    } else {
      j := j + 1;
    }
    l := l + 1;
  }
  assert i + j == l;
}

// remaining goals of -teq -simplify:
// none
