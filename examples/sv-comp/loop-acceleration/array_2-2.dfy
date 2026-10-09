// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-acceleration/array_2-2.dfy
// SV-COMP ReachSafety-Loops/loop-acceleration/array_2-2.yml (expected: safe), translated from the C program by
// hand: B is overwritten by a copy of A, and A[1024] == B[1024] is checked (array_2-2-simple is a variant)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (array_2-2-simple is a variant,
// array_2-1 and the other array_* with -1 are unsafe)

method main() {
  var i: int;
  var v: int;
  var tmp: int;
  var A: array<int, int>;
  var B: array<int, int>;
  i := 0;
  while i < 2048 {
    havoc v;
    A := A[i := v];
    havoc v;
    B := B[i := v];
    i := i + 1;
  }
  i := 0;
  while i < 2048 {
    tmp := A[i];
    B := B[i := tmp];
    i := i + 1;
  }
  assert A[2048 / 2] == B[2048 / 2];
}

// remaining goals of -teq -simplify:
// none
