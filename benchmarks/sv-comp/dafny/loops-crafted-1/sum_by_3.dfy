// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/loops-crafted-1/sum_by_3.dfy
// SV-COMP loops-crafted-1/sum_by_3.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: i, j, k count up to n in three loops, each starting at the previous one, and their average
// is checked to be at most SIZE
//
// findings: the functions truth, quotient, and remainder of the C prelude in the output of -print dfy are written
// as != 0, /, and % on the nonnegative values, and the havoc of unsigned values, printed as spec, as havoc and
// assume; the average (i + j + k) / 3 of three equal values is 3 * n / 3, which a lemma cancels, and -split splits
// the hypothesis n == 0 || n == N of the number of iterations; closed (no output)

// cancellation of the factor 3 in a division (not about traces)
lemma {:rw} {:teq} lemma_1(x: int)
  ensures (3 * x) / 3 == x

method main() returns (result: int)
{
  var n: int, i: int, k: int, j: int;
  n := *;
  assume 0 <= n;
  i := 0;
  while i < n {
    i := i + 1;
  }
  j := i;
  while j < n {
    j := j + 1;
  }
  k := j;
  while k < n {
    k := k + 1;
  }
  assert (quot(i + j + k, 3)) <= n;
  result := 0;
  return;
}

// remaining goals of -teq -simplify -split -simplify:
// none
