// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/sorting_bubblesort_ground-1.dfy
// SV-COMP array-examples/sorting_bubblesort_ground-1.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of sorting_bubblesort_ground-2 with other constants or assertions;
// checks a[x] <= a[y]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var a: array<int, int>;
  var swapped: int;
  var x: int;
  var y: int;
  var j: int;
  var i: int;
  var t: int;
  assume 0 < N;
  j := 0;
  while j < N {
    tmp₁ := *;
    a := a[j := tmp₁];
    j := j + 1;
  }
  swapped := 1;
  while (swapped != 0) {
    swapped := 0;
    i := 1;
    while i < N {
      if a[i - 1] > a[i] {
        t := a[i];
        a := a[i := a[i - 1]];
        a := a[i - 1 := t];
        swapped := 1;
      }
      i := i + 1;
    }
  }
  x := 0;
  while x < N {
    y := x + 1;
    while y < N {
      assert a[x] <= a[y];
      y := y + 1;
    }
    x := x + 1;
  }
  result := 0;
  return;
}
