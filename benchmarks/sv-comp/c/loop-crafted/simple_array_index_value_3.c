// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_3.c
// SV-COMP loop-crafted/simple_array_index_value_3.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_3.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int SIZE;
  int index;
  int tmp;
  int Array[];
  SIZE = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 < SIZE);
  index = 0;
  tmp = 0;
  while (index < SIZE) {
    Array[index] = tmp;
    index = index + 1;
    tmp = tmp + 2;
  }
  index = 0;
  while (index < SIZE) {
    assert(Array[index] == 2 * index || Array[index] == 0);
    index = index + 1;
  }
}

