// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-new/gauss_sum.dfy
// SV-COMP loop-new/gauss_sum.yml (expected: safe), translated from the C program by hand: the sum
// of 1, ..., n is n * (n + 1) / 2
//
// findings: teq.dfy accelerates the loop of the sum to the closed form (n + n * n) / 2, the remaining goal is
// arithmetic: 2 * sum == n + n * n needs that n + n * n is even; the lemma states that as an equivalence of atoms,
// which closes the goal; stated as an equation of integers, a lemma would rewrite its left-hand side as a term
// instead, and 2 * s inside a polynomial is not matched against the definition of s
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method main() {
  var n: int;
  var sum: int;
  var i: int;
  n := *;
  assume 1 <= n <= 1000;
  sum := 0;
  i := 1;
  while i <= n {
    sum := sum + i;
    i := i + 1;
  }
  assert 2 * sum == n * (n + 1);
}

// remaining goals of -teq -simplify:
// none
