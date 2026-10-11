// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-patterns/array3_pattern.c
// SV-COMP array-patterns/array3_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array3_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array3_pattern.c", 7, "reach_error"); }
extern int __VERIFIER_nondet_int(void);
void assume_abort_if_not(int cond) {
  if (!cond) { abort(); }
}
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: {reach_error(); abort();}
  }
  return;
}

int ARR_SIZE;

int square(int x) {
  int result = __VERIFIER_nondet_int();
  result = x * x;
  return result;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int count = __VERIFIER_nondet_int();
  int num = __VERIFIER_nondet_int();
  int sum1 = __VERIFIER_nondet_int();
  int sum2 = __VERIFIER_nondet_int();
  int temp = __VERIFIER_nondet_int();
  int index = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  ARR_SIZE = tmp_1;
  assume_abort_if_not(ARR_SIZE > 0);
  count = 0;
  num = -1;
  sum1 = 0;
  sum2 = 0;
  count = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && ARR_SIZE <= N && N <= 268435455);
  int array1[N];
  int array2[N];
  while (count < ARR_SIZE) {
    array1[count] = 0;
    array2[count] = 0;
    count = count + 1;
  }
  while (1 != 0) {
    index = __VERIFIER_nondet_int();
    assume_abort_if_not(index >= 0 && index < ARR_SIZE);
    array1[index] = array1[index] + num * (num * index);
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
  __VERIFIER_assert(sum1 == sum2);
  result = 0;
  return result;
}

