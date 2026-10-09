// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-crafted/simple_array_index_value_4.dfy
// SV-COMP ReachSafety-Loops/loop-crafted/simple_array_index_value_4.yml (expected: safe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of simple_array_index_value_2 with other constants or assertions;
// checks (index1 < 100000) && (index2 < 100000); array[index1] == array[index2]
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 100000

method main() returns (result: int) {
  var N: int;
  var tmp₁: int;
  assume 0 < N;
  {
    var array: array<int, int>;
    var index1: int;
    var index2: int;
    var loop_entered: int;
    loop_entered := 0;
    {
      var i: int;
      i := 0;
      while i < N {
        tmp₁ := *;
  assume 0 <= tmp₁;
        array := array[i := tmp₁];
        i := i + 1;
      }
    }
    index1 := *;
    assume 0 <= index1;
    assume index1 < N;
    index2 := *;
    assume 0 <= index2;
    assume index2 < N;
    while index1 < index2 {
      assert index1 < N && index2 < N;
      assume array[index1] == array[index2];
      index1 := index1 + 1;
      index2 := index2 - 1;
      loop_entered := 1;
    }
    if (loop_entered != 0) {
      while index2 < index1 {
        assert array[index1] == array[index2];
        index2 := index2 + 1;
        index1 := index1 - 1;
      }
    }
  }
}
