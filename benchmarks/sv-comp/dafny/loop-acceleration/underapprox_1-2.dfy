// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-acceleration/underapprox_1-2.dfy
// SV-COMP loop-acceleration/underapprox_1-2.yml (expected: safe), translated from the C program by hand: y is
// doubled 6 times, starting from 1, and a power of 2 is not divisible by 3
//
// findings: y is doubled in each iteration, a geometric sequence, which the lemma accelerates to x0 * pow(c, n)
// with the auxiliary function pow, which is not unfolded, such that the iterations are not unrolled, and
// pow_two_mod_three states that powers of 2 are not divisible by 3; closed (no output)
// note: both lemmas are local again (Oct 23, 2026): they were part of teq.dfy, then left in the legacy file as
// specific to these tasks; pow is declared by teq:arithmetic, which the benchmark definitions include
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 6


// a value multiplied by c in each iteration, a geometric sequence
lemma {:rw} current_trace_geometric(x0: int, c: int, n: Nat)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋ do x, k :: c * x)) == x0 * pow(c, n)

// a power of 2 is not divisible by 3
lemma {:rw} pow_two_mod_three(n: Nat)
  ensures (pow(2, n) % 3 == 0) <==> false

method main() {
  var N: int;
  var x: int;
  var y: int;
  assume 0 < N;
  x := 0;
  y := 1;
  while x < N {
    x := x + 1;
    y := y * 2;
  }
  assert rem(y, 3) != 0;
}

// remaining goals of -teq -simplify:
// none
