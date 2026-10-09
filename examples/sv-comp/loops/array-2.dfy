// ./Cuvee.sh -teq -simplify examples/sv-comp/loops/array-2.dfy
// SV-COMP loops/array-2.yml (expected: unsafe), translated from the C program by ./Cuvee.sh
// -print dfy: a variant of array-1 with other constants or assertions; checks array[0]>menor

method main() returns (result: int) {
  var tmp₁: int;
  {
    var SIZE: int;
    var j: int;
    var k: int;
    var array: array<int, int>;
    var menor: int;
    SIZE := 1;
    menor := *;
    j := 0;
    while j < SIZE {
      tmp₁ := *;
      array := array[j := tmp₁];
      if array[j] <= menor {
        menor := array[j];
      }
      j := j + 1;
    }
    assert array[0] > menor;
    result := 0;
    return;
  }
}
