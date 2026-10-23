// ./Cuvee.sh -teq -prove benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_1-2.dfy
// SV-COMP loop-crafted/simple_array_index_value_1-2.yml (expected: unsafe), translated from the C
// program by ./Cuvee.sh -print dfy: a variant of simple_array_index_value_1-1 with other constants or assertions;
// checks tmp < 10000 && array[tmp] == tmp

method main() returns (result: int) {
  var N: int;
  var array: array<int, int>;
  var index: int;
  var tmp: int;
  assume 0 < N;
  index := 0;
  tmp := 0;
  while (1 != 0) {
    index := *;
  assume 0 <= index;
    if index >= N {
      break;
    }
    array := array[index := index];
    tmp := index;
  }
  assert tmp < N && array[tmp] == tmp;
}
