// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-cav19/array_init_var_plus_ind.dfy
// SV-COMP array-cav19/array_init_var_plus_ind.yml (expected: safe), translated from the C program
// by hand: a[i] = j, where j accumulates the indices 0 + 1 + ... + (i - 1), in a loop that may stop early (a
// nondeterministic break), and a[k] >= 0 is checked below the exit
//
// findings: teq.dfy sums j as (k + k * k) / 2; a lemma in the normal form of the simplifier states that it is
// nonnegative; closed (no output)
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var i: int;
  var j: int;
  var k: int;
  var x: int;
  var N: int;
  var a: array<int, int>;
  N := *;
  assume 0 < N;
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
