// ./Cuvee.sh -teq -simplify examples/sv-comp/array-examples/sorting_bubblesort_2_ground.dfy
// SV-COMP ReachSafety-Arrays/array-examples/sorting_bubblesort_2_ground.yml (expected: unsafe), translated from the
// C program by ./Cuvee.sh -print dfy: a program of the folder; checks a[x] <= a[y]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  assume 0 < N;
  {
    var a: array<int, int>;
    var swapped: int;
    var x: int;
    var y: int;
    {
      var j: int;
      j := 0;
      while j < N {
        tmp₁ := *;
        a := a[j := tmp₁];
        j := j + 1;
      }
    }
    swapped := 1;
    while (swapped != 0) {
      var i: int;
      swapped := 0;
      i := 1;
      while i < N {
        if a[i] > a[i - 1] {
          var t: int;
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
}
