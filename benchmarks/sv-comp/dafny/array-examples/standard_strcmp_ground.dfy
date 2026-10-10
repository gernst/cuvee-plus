// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/array-examples/standard_strcmp_ground.dfy
// SV-COMP array-examples/standard_strcmp_ground.yml (expected: safe), translated from the C program by hand:
// _strcmp (inlined) returns 1 at the first position where a and b differ, and 0 otherwise, in which case they
// are checked to agree everywhere; the return from the loop is a break with the result
//
// findings: the comparison breaks at the first difference; -teq turns c == 0 into the iteration constraint that
// both agree, which the lemmas of teq.dfy abstract by agree_prefix and instantiate at the position; closed
// (no output)
// note: its lemmas are part of teq.dfy now (agree_prefix_def, earlier_agree_prefix) and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() {
  var N: int;
  var i: int;
  var x: int;
  var v: int;
  var c: int;
  var a: array<int, int>;
  var b: array<int, int>;
  assume 0 < N;
  i := 0;
  while i < N {
    v := *;
    a := a[i := v];
    v := *;
    b := b[i := v];
    i := i + 1;
  }
  c := 0;
  i := 0;
  while i < N {
    if b[i] != a[i] {
      c := 1;
      break;
    }
    i := i + 1;
  }
  if c == 0 {
    x := 0;
    while x < N {
      assert a[x] == b[x];
      x := x + 1;
    }
  }
}

// remaining goals of -teq -simplify:
// none
