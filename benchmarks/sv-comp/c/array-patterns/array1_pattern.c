// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-patterns/array1_pattern.c
// SV-COMP array-patterns/array1_pattern.yml, translated from benchmarks/sv-comp/dafny/array-patterns/array1_pattern.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array1_pattern.c", 7, "reach_error"); }
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

void main(void) {
  int N = __VERIFIER_nondet_int();
  int count = __VERIFIER_nondet_int();
  int num = __VERIFIER_nondet_int();
  int temp = __VERIFIER_nondet_int();
  int index = __VERIFIER_nondet_int();
  int sum = __VERIFIER_nondet_int();
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  int array1[N], array2[N];
  assume_abort_if_not(N > 0);
  num = -1;
  sum = 0;
  count = 0;
  while (count < N) {
    array1[count] = 0;
    array2[count] = 0;
    count = count + 1;
  }
  while (1) {
    index = __VERIFIER_nondet_int();
    assume_abort_if_not(index >= 0 && index < N);
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
  __VERIFIER_assert(sum == 0);
}

