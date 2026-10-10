// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/loop-invgen/seq-3.dfy
// SV-COMP loop-invgen/seq-3.yml (expected: safe), translated from the C program by hand: k counts
// up in two loops, to n0 and n1, both arbitrary and possibly negative, then down in a loop to n0 + n1, and is
// positive before each decrement
//
// findings: teq.dfy accelerates all three loops; -split splits the disjunctions of their exits, and the remaining
// case n0 <= 0, n1 <= 0, 0 < n0 + n1 is inconsistent, which the simplifier does not find, since n0 + n1 is no
// difference constraint (see TODO.md); a lemma states it

// two values that are not positive have a sum that is not positive, which is no difference constraint; stated as an
// inconsistent conjunction, since the side conditions of a rule 0 < a + b would be decided by the rule itself again
lemma {:rw} {:teq} lemma_1(a: int, b: int, R: bool)
  ensures (R && a <= 0 && b <= 0 && 0 < a + b) <==> false

method main() {
  var n0: int;
  var n1: int;
  var i0: int;
  var i1: int;
  var j1: int;
  var k: int;
  i0 := 0;
  k := 0;
  n0 := *;
  n1 := *;
  assume -1000000 <= n0;
  assume -1000000 <= n1;
  while i0 < n0 {
    i0 := i0 + 1;
    k := k + 1;
  }
  i1 := 0;
  while i1 < n1 {
    i1 := i1 + 1;
    k := k + 1;
  }
  j1 := 0;
  while j1 < n0 + n1 {
    assert k > 0;
    j1 := j1 + 1;
    k := k - 1;
  }
}

// remaining goals of -teq -simplify -split -simplify:
// goal
//   forall n0₇: int, n1₈: int ::
//     !(0 <= n0₇ + 1000000
//         && 0 <= n1₈ + 1000000
//         && n0₇ <= 0
//         && n1₈ <= 0 < n0₇ + n1₈)
