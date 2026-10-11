// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/loops/matrix-2-2.c
// SV-COMP loops/matrix-2-2.yml, translated from benchmarks/sv-comp/dafny/loops/matrix-2-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "matrix-2-2.c", 7, "reach_error"); }
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
  int N_LIN = __VERIFIER_nondet_int();
  int N_COL = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int maior = __VERIFIER_nondet_int();
  tmp_1 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_1);
  N_LIN = tmp_1;
  tmp_2 = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= tmp_2);
  N_COL = tmp_2;
  if (N_LIN >= 1000000000 || N_COL >= 1000000000) {
    result = 0;
    return result;
  }
  maior = __VERIFIER_nondet_int();
  j = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N_COL <= N && N_LIN <= N && N <= 16383);
  int matriz[N][N];
  while (j < N_COL) {
    k = 0;
    while (k < N_LIN) {
      tmp_3 = __VERIFIER_nondet_int();
      matriz[j][k] = tmp_3;
      if (matriz[j][k] > maior) {
        maior = matriz[j][k];
      }
      k = k + 1;
    }
    j = j + 1;
  }
  j = 0;
  while (j < N_COL) {
    k = 0;
    while (k < N_LIN) {
      __VERIFIER_assert(matriz[j][k] < maior);
      k = k + 1;
    }
    j = j + 1;
  }
}

