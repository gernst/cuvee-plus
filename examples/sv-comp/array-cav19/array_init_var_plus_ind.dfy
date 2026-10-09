// ./Cuvee.sh -teq -simplify examples/sv-comp/array-cav19/array_init_var_plus_ind.dfy
// SV-COMP ReachSafety-Arrays/array-cav19/array_init_var_plus_ind.yml (expected: safe), translated from the C program
// by hand: a[i] = j, where j accumulates the indices 0 + 1 + ... + (i - 1), in a loop that may stop early (a
// nondeterministic break), and a[k] >= 0 is checked below the exit
//
// findings: teq.dfy sums j as (k + k * k) / 2; a lemma in the normal form of the simplifier states that it is
// nonnegative; closed (no output)

// the sum 0 + 1 + ... + x of a nonnegative x is nonnegative, in the normal form of the simplifier (arithmetic, not
// about traces); the left-hand side is a comparison
lemma {:rw} {:free} {:teq} forall x: int ::
  if 0 <= x
  then 0 <= (x + x * x) / 2

method main() {
  var i: int;
  var j: int;
  var k: int;
  var x: int;
  var N: int;
  var a: array<int, int>;
  N := 100000;
  j := 0;
  i := 0;
  while i < N {
    x := *;
    if x != 0 {
      break;
    }
    a := a[i := j];
    j := j + i;
    i := i + 1;
  }
  k := 1;
  while k < i {
    assert a[k] >= 0;
    k := k + 1;
  }
}

// remaining goals of -teq -simplify:
// none
