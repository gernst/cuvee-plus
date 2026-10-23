// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/loops/matrix-1.c
// SV-COMP loops/matrix-1.yml, translated from benchmarks/sv-comp/dafny/loops/matrix-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "matrix-1.c", 7, "reach_error"); }
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
  int N_LIN = __VERIFIER_nondet_int();
  int N_COL = __VERIFIER_nondet_int();
  int j = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  int maior = __VERIFIER_nondet_int();
  N_LIN = 1;
  N_COL = 1;
  maior = __VERIFIER_nondet_int();
  j = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N_COL <= N && N_LIN <= N && 0 < N && N <= 16383);
  int matriz[N][N];
  while (j < N_COL) {
    k = 0;
    while (k < N_LIN) {
      tmp_1 = __VERIFIER_nondet_int();
      matriz[j][k] = tmp_1;
      if (matriz[j][k] >= maior) {
        maior = matriz[j][k];
      }
      k = k + 1;
    }
    j = j + 1;
  }
  __VERIFIER_assert(matriz[0][0] <= maior);
  result = 0;
  return result;
}

