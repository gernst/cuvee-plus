// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loops/eureka_05.dfy
// SV-COMP loops/eureka_05.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks array[i]==i
// note: the global variables of the C program are local, and the array that the selection sort sorts, global
// in C, is not initialized; main fills and checks a local array of the same name, and SelectionSort is inlined
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 5 (SIZE), the value of n

method main() returns (result: int) {
  var array: array<int, int>;
  var n: int;
  var N: int;
  var array₁: array<int, int>;
  var i: int;
  var lh: int;
  var rh: int;
  var j: int;
  var temp: int;
  assume 0 < N;
  n := N;
  i := N - 1;
  while i >= 0 {
    array₁ := array₁[i := i];
    i := i - 1;
  }
  lh := 0;
  while lh < n {
    rh := lh;
    j := lh + 1;
    while j < n {
      if array[j] < array[rh] {
        rh := j;
      }
      j := j + 1;
    }
    temp := array[lh];
    array := array[lh := array[rh]];
    array := array[rh := temp];
    lh := lh + 1;
  }
  i := 0;
  while i < N {
    assert array₁[i] == i;
    i := i + 1;
  }
}
