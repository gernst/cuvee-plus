// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/array-crafted/zero_sum_m2.dfy
// SV-COMP array-crafted/zero_sum_m2.yml (expected: safe), translated from the C program by hand:
// the elements of an array of shorts of arbitrary size are added to sum twice and subtracted twice, which is 0 then
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output), as zero_sum1 with two loops of
// each kind

method main() {
  var SIZE: int;
  var a: array<int, int>;
  var sum: int;
  var i: int;
  var tmp: int;
  SIZE := *;
  if SIZE > 1 {
    sum := 0;
    i := 0;
    while i < SIZE {
      tmp := *;
      a := a[i := tmp];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum + a[i];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum - a[i];
      i := i + 1;
    }
    i := 0;
    while i < SIZE {
      sum := sum - a[i];
      i := i + 1;
    }
    assert sum == 0;
  }
}

// remaining goals of -teq -simplify:
// none
