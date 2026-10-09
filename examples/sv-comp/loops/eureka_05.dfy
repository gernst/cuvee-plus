// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/eureka_05.dfy
// SV-COMP ReachSafety-Loops/loops/eureka_05.yml (expected: safe), translated from the C program by ./Cuvee.sh
// -print dfy: a program of the folder; checks array[i]==i

// the constant array of the initializers of C, whose values are all x
function constant(x: int): array<int, int>

lemma {:rw} {:free} {:teq} forall x: int, i: int ::
  constant(x)[i] == x

var array: array<int, int>;

var n: int;

method SelectionSort()
  modifies array
{
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
}

method main() returns (result: int)
  modifies array, n
  requires array == constant(0) && n == 0
{
  n := 5;
  {
    var array₁: array<int, int>;
    var i: int;
    i := 5 - 1;
    while i >= 0 {
      array₁ := array₁[i := i];
      i := i - 1;
    }
    SelectionSort();
    i := 0;
    while i < 5 {
      assert array₁[i] == i;
      i := i + 1;
    }
  }
}
