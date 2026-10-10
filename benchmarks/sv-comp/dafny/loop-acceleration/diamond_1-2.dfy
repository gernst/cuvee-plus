// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/loop-acceleration/diamond_1-2.dfy
// SV-COMP loop-acceleration/diamond_1-2.yml (expected: unsafe), translated from the C program by
// hand: the unsafe variant of diamond_1-1, which counts by 1 if y is even and by 2 otherwise
//
// findings: unsafe, not closed with the lemmas of diamond_1-1, as expected: the cases remain where the parity of x
// differs from that of y
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 99

// a trace whose cases are decided by a condition c that is the same in all iterations, i.e., c does not depend
// on the bound variables, which a variable of the lemma cannot capture, is one of two traces, chosen by c
lemma {:rw} {:teq} trace_1(x0: int, i: int, d: int, n: Nat, c: bool, F: (int, int) -> int, G: (int, int) -> int)
  ensures trace(x0, for ⌊counter(i, d, n)⌋ do x, k :: case c => F(x, k) case !c => G(x, k))
    == if c then trace(x0, for ⌊counter(i, d, n)⌋ do x, k :: F(x, k))
       else trace(x0, for ⌊counter(i, d, n)⌋ do x, k :: G(x, k))

// the remainder modulo 2 is 0 or 1
lemma {:rw} {:teq} lemma_1(y: int)
  ensures !(y % 2 == 0) <==> y % 2 == 1

method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := 0;
  y := *;
  assume 0 <= y;
  while x < N {
    if y % 2 == 0 {
      x := x + 1;
    } else {
      x := x + 2;
    }
  }
  assert x % 2 == y % 2;
}

// remaining goals of -teq -simplify -split -simplify:
// goal forall y₃: int :: !(0 <= y₃ && y₃ % 2 == 0)
// goal forall y₃: int :: !(0 <= y₃ && y₃ % 2 == 1)
