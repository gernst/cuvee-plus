// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_init_var_plus_ind2.dfy
// SV-COMP array-cav19/array_init_var_plus_ind2.yml (expected: safe), translated from the C program by hand:
// a[i] = j, where j accumulates 0 + 1 + ... + (i - 1) and k = -j, in a loop that may stop early (a
// nondeterministic break), and a[l] >= k is checked below the exit
//
// findings: as array_init_var_plus_ind, with k == -j: the goal is the sum of two such halves, (x + x * x) / 2 and
// (-x + x * x) / 2, which are nonnegative for all integers x, by lemmas whose left-hand sides are comparisons with
// a further summand d, whose side condition 0 <= d is decided by the same lemmas; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

// the sums 0 + 1 + ... + x and 0 + 1 + ... + (x - 1) are nonnegative for all integers x, also plus a nonnegative d, in
// the normal form of the simplifier (arithmetic, not about traces); the left-hand sides are comparisons
lemma {:rw} {:teq} lemma_1(x: int)
  ensures 0 <= (x + x * x) / 2
lemma {:rw} {:teq} lemma_2(x: int)
  ensures 0 <= (-x + x * x) / 2
lemma {:rw} {:teq} lemma_3(x: int, d: int)
  requires 0 <= d
  ensures 0 <= (x + x * x) / 2 + d
lemma {:rw} {:teq} lemma_4(x: int, d: int)
  requires 0 <= d
  ensures 0 <= (-x + x * x) / 2 + d

method main() {
  var N: int;
  var i: int;
  var j: int;
  var k: int;
  var l: int;
  var x: int;
  var a: array<int, int>;
  assume 0 < N;
  j := 0;
  k := 0;
  i := 0;
  while i < N {
    x := *;
    if x != 0 {
      break;
    }
    a := a[i := j];
    j := j + i;
    k := k - i;
    i := i + 1;
  }
  l := 1;
  while l < i {
    assert a[l] >= k;
    l := l + 1;
  }
}

// remaining goals of -teq -simplify:
// none
