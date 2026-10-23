// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/sum_array-2-2.c
// SV-COMP loops/sum_array-2-2.yml, translated from benchmarks/sv-comp/dafny/loops/sum_array-2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum_array-2-2.c", 7, "reach_error"); }
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

int main(void) {
  int result = __VERIFIER_nondet_int();
  int tmp_1 = __VERIFIER_nondet_int();
  int tmp_2 = __VERIFIER_nondet_int();
  int tmp_3 = __VERIFIER_nondet_int();
  int M = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  M = tmp_1;
  if (M > 1000000) {
    result = 0;
    return result;
  }
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && M <= N && N <= 134217727);
  int A[N], B[N], C[N];
  while (i < M) {
    tmp_2 = __VERIFIER_nondet_int();
    A[i] = tmp_2;
    i = i + 1;
  }
  i = 0;
  while (i < M) {
    tmp_3 = __VERIFIER_nondet_int();
    B[i] = tmp_3;
    i = i + 1;
  }
  i = 0;
  while (i < M) {
    C[i] = A[i] + B[i];
    i = i + 1;
  }
  i = 0;
  while (i < M) {
    __VERIFIER_assert(C[i] == A[i] + B[i]);
    i = i + 1;
  }
}

