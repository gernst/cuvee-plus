// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/while_infinite_loop_3.dfy
// SV-COMP ReachSafety-Loops/loops/while_infinite_loop_3.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: an infinite loop calls eval, which sets the global x to 0 in a loop that it leaves at
// once, and checks x == 0, and the unreachable end checks x != 0
//
// findings: error: eval contains a loop that is left by break in its first iteration, on which -teq fails with an
// internal error (empty.reduceLeft, and head of empty list with -simplify), also on a minimal loop while true { x
// := 0; break; } (see TODO.md)

var x: int;

method eval()
  modifies x
{
  {
    while ((1) != 0)
      modifies x
    {
      x := 0;
      break;
    }
    return;
  }
}

method main() returns (result: int)
  modifies x
  requires x == 0
{
  x := 0;
  {
    while ((1) != 0)
      modifies x
    {
      eval();
      assert x == 0;
    }
    assert x != 0;
    result := 0;
    return;
  }
}

// remaining goals of -teq -simplify:
// error "internal error" "NoSuchElementException" "head of empty list"
