// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loop-crafted/simple_array_index_value_4.c
// SV-COMP loop-crafted/simple_array_index_value_4.yml, translated from benchmarks/sv-comp/dafny/loop-crafted/simple_array_index_value_4.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int main(void) {
  int result;
  int N;
  int tmp_1;
  int Array[];
  int index1;
  int index2;
  int loop_entered;
  int i;
  __VERIFIER_assume(0 < N);
  loop_entered = 0;
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    __VERIFIER_assume(0 <= tmp_1);
    Array[i] = tmp_1;
    i = i + 1;
  }
  index1 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= index1);
  __VERIFIER_assume(index1 < N);
  index2 = __VERIFIER_nondet_int();
  __VERIFIER_assume(0 <= index2);
  __VERIFIER_assume(index2 < N);
  while (index1 < index2) {
    assert(index1 < N && index2 < N);
    __VERIFIER_assume(Array[index1] == Array[index2]);
    index1 = index1 + 1;
    index2 = index2 - 1;
    loop_entered = 1;
  }
  if (loop_entered != 0) {
    while (index2 < index1) {
      assert(Array[index1] == Array[index2]);
      index2 = index2 + 1;
      index1 = index1 - 1;
    }
  }
}

