// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-crafted/simple_array_index_value_1-2.dfy
// SV-COMP ReachSafety-Loops/loop-crafted/simple_array_index_value_1-2.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of simple_array_index_value_1-1 with other constants or assertions;
// checks tmp < 10000 && array[tmp] == tmp

method main() returns (result: int) {
  {
    var array: array<int, int>;
    var index: int;
    var tmp: int;
    index := 0;
    tmp := 0;
    while (1 != 0) {
      index := *;
    assume 0 <= index;
      if index >= 10000 {
        break;
      }
      array := array[index := index];
      tmp := index;
    }
    assert tmp < 10000 && array[tmp] == tmp;
  }
}
