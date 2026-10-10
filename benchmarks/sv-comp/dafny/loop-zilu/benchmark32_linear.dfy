// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-zilu/benchmark32_linear.dfy
// SV-COMP loop-zilu/benchmark32_linear.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: x alternates between 1 and 2, if it is one of them, and x <= 8 is checked
//
// findings: a value that swaps 1 and 2 and keeps all others, a trace with three cases, stays one of them by a lemma
// generic in the two values, stated as a bound with a comparison as its left-hand side; closed (no output)

// a value that swaps a and b, and keeps all others, stays one of them if it starts as one of them, hence below a
// common bound c; the left-hand side is a comparison
lemma {:rw} {:teq} current_1(x0: int, n: Nat, a: int, b: int, c: int)
  requires (x0 == a || x0 == b) && a <= c && b <= c
  ensures
    current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: case x == a => b case x == b => a case x != a && x != b => x)) <= c

method main() returns (result: int) {
  var tmp₁: int, tmp₂: bool;
  var x: int;
  tmp₁ := *;
  x := tmp₁;
  if !(x == 1 || x == 2) {
    result := 0;
    return;
  }
  while true {
    tmp₂ := *;
    if !tmp₂ {
      break;
    }
    if x == 1 {
      x := 2;
    } else if x == 2 {
      x := 1;
    }
  }
  assert x <= 8;
  result := 0;
  return;
}

// remaining goals of -teq -simplify:
// none
