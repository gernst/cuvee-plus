// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loops/linear_search.dfy
// SV-COMP loops/linear_search.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks linear_search(a,SIZE,3)
// note: the arrays are not initialized (the values of C, which constant(0) gave them), since the result does not
// depend on them

var SIZE: int;

method linear_search(a: array<int, int>, n: int, q: int) returns (result: int) {
  var j: int;
  j := 0;
  while j < n && a[j] != q {
    j := j + 1;
    if j == 20 {
      j := -1;
    }
  }
  if j < SIZE {
    result := 1;
    return;
  } else {
    result := 0;
    return;
  }
}

method main() returns (result: int)
  modifies SIZE
  requires SIZE == 0
{
  var tmp₁: int;
  var tmp₂: int;
  var a: array<int, int>;
  tmp₁ := *;
  assume 0 <= tmp₁;
  SIZE := (quot(tmp₁, 2)) + 1;
  if SIZE > 1 {
    a := a[(quot(SIZE, 2)) := 3];
    tmp₂ := linear_search(a, SIZE, 3);
    assert (tmp₂ != 0);
  }
}
