// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/sorting_selectionsort_2_ground.dfy
// SV-COMP array-examples/sorting_selectionsort_2_ground.yml (expected: unsafe), translated from
// the C program by ./Cuvee.sh -print dfy: a program of the folder; checks a[x] <= a[y]; a[x] >= a[i]; a[x] <= a[y]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  var a: array<int, int>;
  var i: int;
  var x: int;
  var y: int;
  var k: int;
  var s: int;
  var tmp: int;
  assume 0 < N;
  i := 0;
  i := 0;
  while i < N {
    tmp₁ := *;
    a := a[i := tmp₁];
    i := i + 1;
  }
  i := 0;
  while i < N {
    k := i;
    s := i + 1;
    while k < N {
      if a[k] > a[s] {
        s := k;
      }
      k := k + 1;
    }
    if s != i {
      tmp := a[s];
      a := a[s := a[i]];
      a := a[i := tmp];
    }
    x := 0;
    while x < i {
      y := x + 1;
      while y < i {
        assert a[x] <= a[y];
        y := y + 1;
      }
      x := x + 1;
    }
    x := i + 1;
    while x < N {
      assert a[x] >= a[i];
      x := x + 1;
    }
    i := i + 1;
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
