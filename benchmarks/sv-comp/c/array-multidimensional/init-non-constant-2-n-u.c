// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-multidimensional/init-non-constant-2-n-u.c
// SV-COMP array-multidimensional/init-non-constant-2-n-u.yml, translated from benchmarks/sv-comp/dafny/array-multidimensional/init-non-constant-2-n-u.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "init-non-constant-2-n-u.c", 7, "reach_error"); }
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
  int q = __VERIFIER_nondet_int();
  int s = __VERIFIER_nondet_int();
  int C = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  C = tmp_1;
  q = __VERIFIER_nondet_int();
  s = __VERIFIER_nondet_int();
  i = 0;
  j = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && q <= N && s <= N && N <= 16383);
  int A[N][N];
  while (i < q) {
    j = 0;
    while (j < s) {
      A[i][j] = i + j + C;
      j = j + 1;
    }
    i = i + 1;
  }
  i = 0;
  j = 0;
  while (i < q) {
    j = 0;
    while (j < s) {
      __VERIFIER_assert(A[i][j] == i + j + C);
      j = j + 1;
    }
    i = i + 1;
  }
  result = 0;
  return result;
}

