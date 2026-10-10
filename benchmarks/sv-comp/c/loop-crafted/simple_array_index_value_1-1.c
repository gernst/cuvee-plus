// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_1-1.c
// SV-COMP loop-crafted/simple_array_index_value_1-1.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_1-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int SIZE;
  int index;
  int Array[];
  SIZE = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < SIZE);
  index = 0;
  while (index < SIZE) {
    Array[index] = index % 2;
    index = index + 1;
  }
  index = 0;
  while (index < SIZE) {
    if (index % 2 == 0) {
      assert(Array[index] == 0);
    } else {
      assert(Array[index] != 0);
    }
    index = index + 1;
  }
}

