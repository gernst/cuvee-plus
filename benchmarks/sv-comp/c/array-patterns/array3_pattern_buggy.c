// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array3_pattern_buggy.c
// SV-COMP array-patterns/array3_pattern_buggy.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array3_pattern_buggy.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int square(int x) {
  int result;
  result = x * x;
  return result;
}

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int array1[];
  int array2[];
  int count;
  int num;
  int sum1;
  int sum2;
  int temp;
  int index;
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  __VERIFIER_assume(ARR_SIZE > 0);
  count = 0;
  num = -1;
  sum1 = 0;
  sum2 = 0;
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
      array1[index] = array1[index] + num * (num * index);
    }
    array2[ARR_SIZE - 1 - index] = array2[ARR_SIZE - 1 - index] + num * index;
    temp = __VERIFIER_nondet_int();
    if (temp == 0) {
      break;
    }
  }
  count = 0;
  while (count < ARR_SIZE) {
    tmp_2 = square(array1[count]);
    sum1 = sum1 + tmp_2;
    tmp_3 = square(array2[count]);
    sum2 = sum2 + tmp_3;
    count = count + 1;
  }
  assert(sum1 == sum2);
  result = 0;
  return result;
}

