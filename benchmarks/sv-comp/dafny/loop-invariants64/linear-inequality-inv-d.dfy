// ./Cuvee.sh -teq -simplify -split -simplify benchmarks/sv-comp/dafny/loop-invariants64/linear-inequality-inv-d.dfy
// SV-COMP loop-invariants64/linear-inequality-inv-d.yml (expected: safe), translated from the C
// program by hand: as loop-invariants/linear-inequality-inv-a for unsigned int, 0 < n <= 2^32 - 1 values v <= 2^32
// - 1, whose sum (unsigned long) is at most (2^32 - 1)^2
//
// findings: with the lemma current_1 of loop-invariants/linear-inequality-inv-a, below_prefix and nonneg_prefix of teq.dfy, and -split; closed (no output)

// are those of loop-invariants/linear-inequality-inv-a

// the iteration constraints of values chosen between 0 and b in each of n iterations (with a further dependency hs),
// abstracted by the predicates below_prefix and nonneg_prefix of teq.dfy, one lemma each, since a conjunction as a
// left-hand side does not match two conjuncts among others; below first, since the other matches x <= b as 0 <= b - x
lemma {:rw} {:teq} invs_1(n: Nat, b: int, hs: List<int>, xs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs check k, h, x :: x <= b) <==> below_prefix(n, xs, b)
lemma {:rw} {:teq} invs_2(n: Nat, hs: List<int>, xs: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs check k, h, x :: 0 <= x) <==> nonneg_prefix(n, xs)

// the last value of a trace that takes the values xs, and its initial value x0 if there are none
lemma {:rw} {:teq} current_1(x0: int, n: Nat, xs: List<int>)
  ensures current(trace(x0, for ⌊counter(0, 1, n)⌋, xs do v, k, x :: x)) == if n == zero then x0 else earlier(natural(integer(n) - 1), xs)

method main() {
  var M: int;
  var n: int;
  var v: int;
  var s: int;
  var i: int;
  n := *;
  assume 0 <= M;
  assume 0 < n <= M;
  v := 0;
  s := 0;
  i := 0;
  while i < n {
    v := *;
    assume 0 <= v <= M;
    s := s + v;
    i := i + 1;
  }
  assert s >= v;
  assert s <= M * M;
}

// remaining goals of -teq -simplify -split -simplify:
// none
