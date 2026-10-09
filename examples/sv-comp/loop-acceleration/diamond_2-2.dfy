// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/diamond_2-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/diamond_2-2.yml (expected: safe), translated from the C program by
// hand: as diamond_1-1, with ten steps per iteration that depend on the parity of y, by 2 each if y is even, and by
// 1, -2, 2, -2, 2, -4, 4, 2, -4, -4 otherwise, which sum to -5; x is unsigned in C, which wraps around for odd y,
// while it decreases here, such that the loop does not terminate for odd y, and the assertion holds vacuously
//
// findings: -teq crashes with a stack overflow in Subst, presumably from the 2^10 paths of the ten conditionals of
// the body (see TODO.md); for odd y, x decreases in each iteration here, without the wrap-around of unsigned
// integers in C, such that the loop does not terminate and the assertion holds vacuously; no lemma is added

method main() {
  var x: int;
  var y: int;
  x := 0;
  y := *;
  assume 0 <= y;
  while x < 99 {
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + 1;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + -2;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + 2;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + -2;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + 2;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + -4;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + 4;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + 2;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + -4;
    }
    if y % 2 == 0 {
      x := x + 2;
    } else {
      x := x + -4;
    }
  }
  assert x % 2 == y % 2;
}

// remaining goals of -teq -simplify:
// crash: Exception in thread "main" java.lang.StackOverflowError
