// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_2.c
// SV-COMP loop-crafted/simple_array_index_value_2.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int Array[];
  int index;
  int tmp;
  __VERIFIER_assume(0 < N);
  index = 0;
  while (index < N) {
    tmp = __VERIFIER_nondet_int();
    __VERIFIER_assume(tmp > index);
    Array[index] = tmp;
    index = index + 1;
  }
  index = 0;
  while (index < N) {
    assert(Array[index] > index);
    index = index + 1;
  }
}

