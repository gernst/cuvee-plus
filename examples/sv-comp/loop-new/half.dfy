// ./Cuvee.sh -teq -simplify -split -simplify examples/sv-comp/loop-new/half.dfy
// SV-COMP loop-new/half.yml (expected: safe), translated from the C program by hand: n counts the
// even numbers below 2 * k, which are k many
//
// findings: the loop counts the even iterations, which teq.dfy introduces as count(0, maps(... k % 2)) over the
// iterations; count_remainder of teq.dfy, the number of remainders modulo m among 0, ..., n
// - 1, accelerates it, generic in m and
// r; -split splits the disjunction of the exit (n == 0 or n == 2 * k), and a lemma on the division of m * k + r by
// m gives k; closed (no output). Attempt: division as linear bounds (2 * s <= x < 2 * s + 2) leaves a goal that
// needs integer rounding
// note: its lemmas are part of teq.dfy now (count_remainder, div_quotient_remainder) and are removed here

method main() {
  var i: int;
  var n: int;
  var k: int;
  i := 0;
  n := 0;
  k := *;
  assume -1000000 <= k <= 1000000;
  i := 0;
  while i < 2 * k {
    if i % 2 == 0 {
      n := n + 1;
    }
    i := i + 1;
  }
  assert k < 0 || n == k;
}

// remaining goals of -teq -simplify -split -simplify:
// none
