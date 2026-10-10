// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array1_pattern.c
// SV-COMP array-patterns/array1_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array1_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

void main(void) {
  int N;
  int count;
  int num;
  int temp;
  int index;
  int sum;
  int array1[];
  int array2[];
  N = __VERIFIER_nondet_int();
  __VERIFIER_assume(N > 0);
  num = -1;
  sum = 0;
  count = 0;
  while (count < N) {
    array1[count] = 0;
    array2[count] = 0;
    count = count + 1;
  }
  while (true) {
    index = __VERIFIER_nondet_int();
    __VERIFIER_assume(index >= 0 && index < N);
    array1[index] = num * (num * index);
    array2[N - 1 - index] = num * index;
    temp = __VERIFIER_nondet_int();
    if (temp == 0) {
      break;
    }
  }
  count = 0;
  while (count < N) {
    sum = sum + array1[count] + array2[count];
    count = count + 1;
  }
  assert(sum == 0);
}

