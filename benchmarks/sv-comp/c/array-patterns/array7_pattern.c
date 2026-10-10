// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array7_pattern.c
// SV-COMP array-patterns/array7_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array7_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
  int tmp_3;
  int array1[];
  int array2[];
  int count;
  int num;
  int sum;
  int temp;
  int index;
  int pivot;
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
    tmp_2 = __VERIFIER_nondet_int();
    index = tmp_2;
    tmp_3 = __VERIFIER_nondet_int();
    pivot = tmp_3;
    __VERIFIER_assume(pivot > 0);
    __VERIFIER_assume(index >= pivot && index < ARR_SIZE - pivot);
    array1[index] = array1[index - pivot] + array1[index + pivot];
    array2[index] = array2[index - pivot] + array2[index + pivot];
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

