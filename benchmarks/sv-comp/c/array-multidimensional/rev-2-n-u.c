// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-multidimensional/rev-2-n-u.c
// SV-COMP array-multidimensional/rev-2-n-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/rev-2-n-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "rev-2-n-u.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int m = __VERIFIER_nondet_int();
  int n = __VERIFIER_nondet_int();
  m = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < m);
  n = __VERIFIER_nondet_int();
  assume_abort_if_not(0 < n);
  i = 0;
  j = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && m <= N && n <= N && N <= 16383);
  int A[N][N];
  int B[N][N];
  while (i < m) {
    j = 0;
    while (j < n) {
      tmp_1 = __VERIFIER_nondet_int();
      B[i][j] = tmp_1;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      A[i][j] = B[m - i - 1][n - j - 1];
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < m) {
    j = 0;
    while (j < n) {
      __VERIFIER_assert(A[i][j] == B[m - i - 1][n - j - 1]);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

