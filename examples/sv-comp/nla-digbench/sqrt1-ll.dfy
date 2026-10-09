// ./Cuvee.sh -teq -simplify examples/sv-comp/nla-digbench/sqrt1-ll.dfy
// SV-COMP nla-digbench/sqrt1-ll.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: the integer square root a of n by the sum s of the odd numbers t, with the invariants checked in and
// after the loop
//
// findings: the odd numbers t and their sums s are counters and sums, and the remaining arithmetic is the halving
// (4 * x + 2 * x * x) / 2 == 2 * x + x * x in the normal form of the simplifier; closed (no output)
// note: 1 of its lemmas are part of teq.dfy now and are removed here

method assume_abort_if_not(cond: int) {
  {
    if !((cond) != 0) {
      assume false;
    }
  }
}

method main() returns (result: int) {
  {
    var n: int, a: int, s: int, t: int;
    n := *;
    a := 0;
    s := 1;
    t := 1;
    while ((1) != 0) {
      assert t == 2 * a + 1;
      assert s == (a + 1) * (a + 1);
      assert t * t - 4 * s + 2 * t + 1 == 0;
      if !(s <= n) {
        break;
      }
      a := a + 1;
      t := t + 2;
      s := s + t;
    }
    assert t == 2 * a + 1;
    assert s == (a + 1) * (a + 1);
    assert t * t - 4 * s + 2 * t + 1 == 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// none
