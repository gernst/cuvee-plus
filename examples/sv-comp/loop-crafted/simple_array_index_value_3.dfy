// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-crafted/simple_array_index_value_3.dfy
// SV-COMP ReachSafety-Loops/loop-crafted/simple_array_index_value_3.yml (expected: safe), translated from the C
// program by hand: array[i] = 2 i, by a value tmp that grows by 2, checked to be 2 i or 0
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (simple_array_index_value_4
// compares an array from both ends, by two indices, and is not translated)

method main() {
  var SIZE: int;
  var index: int;
  var tmp: int;
  var array: array<int, int>;
  SIZE := 10000;
  index := 0;
  tmp := 0;
  while index < SIZE {
    array := array[index := tmp];
    index := index + 1;
    tmp := tmp + 2;
  }
  index := 0;
  while index < SIZE {
    assert array[index] == 2 * index || array[index] == 0;
    index := index + 1;
  }
}

// remaining goals of -teq -simplify:
// none
