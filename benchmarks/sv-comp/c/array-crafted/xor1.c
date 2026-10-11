// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-crafted/xor1.c
// SV-COMP array-crafted/xor1.yml, translated from benchmarks/sv-comp/dafny/array-crafted/xor1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "xor1.c", 7, "reach_error"); }
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

int xor(int x[], int N) {
  int result = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int res = __VERIFIER_nondet_int();
  res = x[0];
  i = 1;
  while (i < N) {
    res = res ^ x[i];
    i = i + 1;
  }
  result = res;
  return result;
}

int main(void) {
  int result = __VERIFIER_nondet_int();
  int N = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int temp = __VERIFIER_nondet_int();
  int ret = __VERIFIER_nondet_int();
  int ret2 = __VERIFIER_nondet_int();
  int ret5 = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int x[N];
  assume_abort_if_not(1 < N);
  i = 0;
  while (i < N) {
    tmp_1 = __VERIFIER_nondet_int();
    x[i] = tmp_1;
    i = i + 1;
  }
  ret = xor(x, N);
  temp = x[0];
  x[0] = x[1];
  x[1] = temp;
  ret2 = xor(x, N);
  temp = x[0];
  i = 0;
  while (i < N - 1) {
    x[i] = x[i + 1];
    i = i + 1;
  }
  x[N - 1] = temp;
  ret5 = xor(x, N);
  if (ret != ret2 || ret != ret5) {
    __VERIFIER_assert(0);
  }
  result = 1;
  return result;
}

