// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/eureka_05.dfy
// SV-COMP loops/eureka_05.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks array[i]==i
// note: the global array is not initialized (requires array == constant(0)), since main fills and checks a local
// array of the same name and SelectionSort sorts the global one
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 5 (SIZE), the value of n

var array: array<int, int>;

var n: int;

method SelectionSort()
  modifies array
{
  var lh: int;
  var rh: int;
  var i: int;
  var temp: int;
  lh := 0;
  while lh < n
    modifies array
  {
    rh := lh;
    i := lh + 1;
    while i < n {
      if array[i] < array[rh] {
        rh := i;
      }
      i := i + 1;
    }
    temp := array[lh];
    array := array[lh := array[rh]];
    array := array[rh := temp];
    lh := lh + 1;
  }
}

method main() returns (result: int)
  modifies array, n
  requires n == 0
{
  var N: int;
  var array₁: array<int, int>;
  var i: int;
  assume 0 < N;
  n := N;
  i := N - 1;
  while i >= 0 {
    array₁ := array₁[i := i];
    i := i - 1;
  }
  SelectionSort();
  i := 0;
  while i < N {
    assert array₁[i] == i;
    i := i + 1;
  }
}
