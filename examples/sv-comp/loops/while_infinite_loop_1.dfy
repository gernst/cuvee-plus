// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/while_infinite_loop_1.dfy
// SV-COMP loops/while_infinite_loop_1.yml (expected: safe), translated from the C program by
// ./Cuvee.sh -print dfy: an infinite loop checks x == 0, which stays 0, and the unreachable end checks x != 0
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output): the end after the infinite loop
// is unreachable

method main() returns (result: int) {
  {
    var x: int;
    x := 0;
    while ((1) != 0) {
      assert x == 0;
    }
    assert x != 0;
  }
}

// remaining goals of -teq -simplify:
// none
