// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/sorting_selectionsort_ground-2.dfy
// SV-COMP array-examples/sorting_selectionsort_ground-2.yml (expected: safe), translated from
// the C program by ./Cuvee.sh -print dfy: a variant of sorting_selectionsort_ground-1 with other constants or
// assertions; checks a[x] <= a[y]; a[x] >= a[i]; a[x] <= a[y]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₂: int;
  assume 0 < N;
  {
    var a: array<int, int>;
    var i: int;
    var x: int;
    var y: int;
    i := 0;
    {
      var i₁: int;
      i₁ := 0;
      while i₁ < N {
        tmp₂ := *;
        a := a[i₁ := tmp₂];
        i₁ := i₁ + 1;
      }
    }
    i := 0;
    while i < N {
      var k: int;
      var s: int;
      k := i + 1;
      s := i;
      while k < N {
        if a[k] < a[s] {
          s := k;
        }
        k := k + 1;
      }
      if s != i {
        var tmp: int;
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
      x := i;
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
}
