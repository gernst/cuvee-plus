// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-cav19/array_init_pair_symmetr2.dfy
// SV-COMP array-cav19/array_init_pair_symmetr2.yml (expected: safe), translated from the C program by hand:
// a[i] = x and b[i] = y for values x > y chosen in each iteration, c[i] = a[i] - b[i], and c[i] > 0 is checked
//
// findings: the pairs x > y chosen in each iteration are an iteration constraint over two dependencies, abstracted
// by the predicate greater and instantiated at the read position by a lemma whose left-hand side is a comparison;
// closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// the first n values of xs are greater than those of ys at the same iterations, an auxiliary predicate, which is not
// defined
predicate {:teq} greater(n: Nat, xs: List<int>, ys: List<int>)

// the iteration constraint of pairs of values x > y chosen in each of n iterations (with a further dependency hs
// that the constraint does not use), abstracted by the predicate greater
lemma {:rw} {:teq} invs_1(n: Nat, hs: List<int>, xs: List<int>, ys: List<int>)
  ensures invs(for ⌊counter(0, 1, n)⌋, hs, xs, ys check k, h, x, y :: y < x) <==> greater(n, xs, ys)

// its instantiation at an iteration j before n; the left-hand side is a comparison, whose side conditions are an
// atom and closed comparisons
lemma {:rw} {:teq} earlier_1(n: Nat, xs: List<int>, ys: List<int>, j: Nat)
  requires greater(n, xs, ys) && integer(j) < integer(n)
  ensures earlier(j, ys) < earlier(j, xs)

method main() {
  var N: int;
  var i: int;
  var x: int;
  var y: int;
  var a: array<int, int>;
  var b: array<int, int>;
  var c: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    x := *;
    y := *;
    assume y < N && y > -N;
    assume x < N && x > -N;
    assume x > y;
    a := a[i := x];
    b := b[i := y];
    i := i + 1;
  }
  i := 0;
  while i < N {
    c := c[i := a[i] - b[i]];
    i := i + 1;
  }
  i := 1;
  while i < N {
    assert c[i] > 0;
    i := i + 1;
  }
}

// remaining goals of -teq -simplify:
// none
