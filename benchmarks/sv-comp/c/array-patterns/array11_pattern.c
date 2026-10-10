// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array11_pattern.c
// SV-COMP array-patterns/array11_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array11_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int main(void) {
  int result;
  int tmp_1;
  int tmp_2;
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
    array1[count] = 0;
    array2[count] = 0;
    count = count + 1;
  }
  while (1 != 0) {
    tmp_2 = __VERIFIER_nondet_int();
    index = tmp_2;
    __VERIFIER_assume(index >= 0 && index < ARR_SIZE);
    array1[index] = num * (num * (num * (num * index)));
    array2[index] = index == ARR_SIZE - 1 ? index : num * index;
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
  assert(sum == 0 || sum + 2 == 2 * ARR_SIZE);
  result = 0;
  return result;
}

