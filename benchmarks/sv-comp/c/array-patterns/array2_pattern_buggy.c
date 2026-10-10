// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array2_pattern_buggy.c
// SV-COMP array-patterns/array2_pattern_buggy.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array2_pattern_buggy.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int main(void) {
  int result;
  int tmp_1;
  int array1[];
  int array2[];
  int count;
  int num;
  int index;
  int temp;
  int sum;
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  __VERIFIER_assume(ARR_SIZE > 0);
  count = 0;
  num = -1;
  sum = 0;
  count = 0;
  while (count < ARR_SIZE) {
    array1[count] = 0;
    array2[count] = 0;
    count = count + 1;
  }
  while (1 != 0) {
    index = __VERIFIER_nondet_int();
    __VERIFIER_assume(index >= 0 && index < ARR_SIZE);
    if (index == 42) {
      array1[index] = array1[index] + 0;
    } else {
      array1[index] = array1[index] + num * num * index;
    }
    array2[ARR_SIZE - 1 - index] = array2[ARR_SIZE - 1 - index] + num * index;
    temp = __VERIFIER_nondet_int();
    if (temp == 0) {
      break;
    }
  }
  count = 0;
  while (count < ARR_SIZE) {
    sum = sum + array1[count] + array2[count];
    count = count + 1;
  }
  assert(sum == 0);
  result = 0;
  return result;
}

