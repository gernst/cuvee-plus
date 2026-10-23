// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-lit/gj2007b.dfy
// SV-COMP loop-lit/gj2007b.yml (expected: safe), translated from the C program by hand: m takes
// some of the values of x = 0, ..., n - 1, and is checked to be in that range if n > 0
//
// findings: m is set to the iteration k in some iterations and kept otherwise; two lemmas, whose left-hand sides
// are comparisons, bound such a value by bounds that hold of its initial value and of all iterations; closed (no
// output)

// a value that is set to the iteration k where C holds, and kept otherwise, is its initial value x0 or one of the
// iterations 0, ..., n - 1, hence within bounds that hold of both (with further dependencies hs and bs); the
// left-hand sides are comparisons
lemma {:rw} {:teq} current_1(x0: int, n: Nat, hs: List<int>, bs: List<int>, C: (int) -> bool)
  requires 0 <= x0
  ensures 0 <= current(trace(x0, for ⌊counter(0, 1, n)⌋, hs, bs do m, k, h, b :: case C(b) => k case !C(b) => m))
lemma {:rw} {:teq} current_2(x0: int, n: Nat, hs: List<int>, bs: List<int>, C: (int) -> bool)
  requires x0 < integer(n)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, hs, bs do m, k, h, b :: case C(b) => k case !C(b) => m)) < integer(n)

method main() {
  var x: int;
  var m: int;
  var n: int;
  var b: int;
  x := 0;
  m := 0;
  n := *;
  while x < n {
    b := *;
    if b != 0 {
      m := x;
    }
    x := x + 1;
  }
  assert m >= 0 || n <= 0;
  assert m < n || n <= 0;
}

// remaining goals of -teq -simplify:
// none
