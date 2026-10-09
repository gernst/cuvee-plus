// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/insertion_sort-1-2.dfy
// SV-COMP loops/insertion_sort-1-2.yml (expected: unsafe), translated from the C program by
// ./Cuvee.sh -print dfy: a variant of insertion_sort-2-2 with other constants or assertions; checks v[k-1]<=v[k]

method main() returns (result: int) {
  var tmp₁: int;
  var tmp₂: int;
  var SIZE: int;
  var i: int;
  var j: int;
  var k: int;
  var key: int;
  var v: array<int, int>;
  tmp₁ := *;
  assume 0 <= tmp₁;
  SIZE := tmp₁;
  if SIZE >= 1000000000 {
    result := 0;
    return;
  }
  j := 0;
  while j < SIZE {
    tmp₂ := *;
    v := v[j := tmp₂];
    j := j + 1;
  }
  j := 1;
  while j < SIZE {
    key := v[j];
    i := j - 1;
    while i >= 0 && v[i] > key {
      if i < 2 {
        v := v[i + 1 := v[i]];
      }
      i := i - 1;
    }
    v := v[i + 1 := key];
    j := j + 1;
  }
  k := 1;
  while k < SIZE {
    assert v[k - 1] <= v[k];
    k := k + 1;
  }
  result := 0;
  return;
}
