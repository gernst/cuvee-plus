// ./Cuvee.sh -teq -simplify examples/sv-comp/loop-crafted/simple_array_index_value_2.dfy
// SV-COMP loop-crafted/simple_array_index_value_2.yml (expected: safe), translated from the C
// program by hand: each element is an arbitrary value above its index, which is checked; unsigned in C, which the
// assumption implies
//
// findings: the iteration constraint of the first loop, the arbitrary value of each iteration exceeds the
// iteration, is abstracted by the auxiliary predicate above_iterations of teq.dfy, and
// instantiated at the positions of the assertions by
// the atom j < earlier(j, ts) (see standard_find_ground-1); closed (no output)
// note: its lemmas are part of teq.dfy now (above_iterations_def, earlier_above_iterations) and are removed here
// note: the concrete loop bounds are symbolic, arbitrary positive values: N for 10000

method main() {
  var N: int;
  var array: array<int, int>;
  var index: int;
  var tmp: int;
  assume 0 < N;
  index := 0;
  while index < N {
    tmp := *;
    assume tmp > index;
    array := array[index := tmp];
    index := index + 1;
  }
  index := 0;
  while index < N {
    assert array[index] > index;
    index := index + 1;
  }
}

// remaining goals of -teq -simplify:
// none
