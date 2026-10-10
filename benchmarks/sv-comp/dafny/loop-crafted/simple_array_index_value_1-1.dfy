// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_1-1.dfy
// SV-COMP loop-crafted/simple_array_index_value_1-1.yml (expected: safe), translated from the C
// program by hand: array[i] = i % 2, checked to be 0 at even and not 0 at odd positions (SIZE elements, unsigned
// int is int)
//
// findings: closed by -teq -simplify with the lemmas of teq.dfy alone (no output) (simple_array_index_value_1-2 is
// an unsafe variant)
// note: the concrete loop bounds are symbolic, arbitrary positive values: SIZE for 1000

method main() {
  var SIZE: int;
  var index: int;
  var array: array<int, int>;
  SIZE := *;
  assume 0 < SIZE;
  index := 0;
  while index < SIZE {
    array := array[index := index % 2];
    index := index + 1;
  }
  index := 0;
  while index < SIZE {
    if index % 2 == 0 {
      assert array[index] == 0;
    } else {
      assert array[index] != 0;
    }
    index := index + 1;
  }
}

// remaining goals of -teq -simplify:
// none
