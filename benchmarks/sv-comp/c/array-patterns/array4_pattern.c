// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array4_pattern.c
// SV-COMP array-patterns/array4_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array4_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

int ARR_SIZE;

int main(void) {
  int result;
  int array1[];
  int array2[];
  int count;
  int num;
  int sum;
  int temp;
  int index1;
  int index2;
  ARR_SIZE = __VERIFIER_nondet_int();
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
  count = 1;
  while (1 != 0) {
    index1 = __VERIFIER_nondet_int();
    index2 = __VERIFIER_nondet_int();
    __VERIFIER_assume(index1 >= 0 && index1 < ARR_SIZE);
    __VERIFIER_assume(index2 >= 0 && index2 < ARR_SIZE);
    __VERIFIER_assume(array1[index1] == 0);
    __VERIFIER_assume(array2[index2] == 0);
    array1[index1] = num * (num * count);
    array2[index2] = num * count;
    if (count == 200) {
      count = 0;
    }
    count = count + 1;
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

