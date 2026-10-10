// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array6_pattern.c
// SV-COMP array-patterns/array6_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array6_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int main(void) {
  int result;
  int tmp_1;
  int array1[];
  int array2[];
  int count;
  int num;
  int sum;
  int temp;
  int index;
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  __VERIFIER_assume(ARR_SIZE > 0);
  count = 0;
  num = -1;
  sum = 0;
  count = 0;
  while (count < ARR_SIZE) {
    array1[count] = num * (num * count);
    array2[count] = num * count;
    count = count + 1;
  }
  while (1 != 0) {
    index = __VERIFIER_nondet_int();
    __VERIFIER_assume(index > 0 && index < ARR_SIZE - 1);
    array1[index] = array1[index - 1] + array1[index + 1];
    array2[index] = array2[index - 1] + array2[index + 1];
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

