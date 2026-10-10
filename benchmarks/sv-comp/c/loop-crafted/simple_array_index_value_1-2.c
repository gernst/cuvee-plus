// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_1-2.c
// SV-COMP loop-crafted/simple_array_index_value_1-2.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_1-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int Array[];
  int index;
  int tmp;
  __VERIFIER_assume(0 < N);
  index = 0;
  tmp = 0;
  while (1 != 0) {
    index = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= index);
    if (index >= N) {
      break;
    }
    Array[index] = index;
    tmp = index;
  }
  assert(tmp < N && Array[tmp] == tmp);
}

