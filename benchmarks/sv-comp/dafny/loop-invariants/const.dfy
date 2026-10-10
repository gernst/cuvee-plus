// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-invariants/const.dfy
// SV-COMP loop-invariants/const.yml (expected: safe), translated from the C program by hand: s
// stays 0, since it is only incremented if it is not 0, which is checked at nondeterministic points
//
// findings: the value s starts at 0 and changes only where it is not 0; a lemma, generic in the change, states that
// it stays at its initial value c; closed (no output)

// a value that starts at c and is changed only where it differs from c stays c
lemma {:rw} {:teq} current_1(c: int, n: Nat, F: (int) -> int)
  ensures current(trace(c, for ⌊counter(0, 1, n)⌋ do s, k :: case s != c => F(s) case s == c => c)) == c

method main() {
  var s: int;
  var b: int;
  var c: int;
  s := 0;
  b := *;
  while b != 0 {
    if s != 0 {
      s := s + 1;
    }
    c := *;
    if c != 0 {
      assert s == 0;
    }
    b := *;
  }
}

// remaining goals of -teq -simplify:
// none
