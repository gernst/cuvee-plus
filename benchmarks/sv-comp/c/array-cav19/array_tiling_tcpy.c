// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-cav19/array_tiling_tcpy.c
// SV-COMP array-cav19/array_tiling_tcpy.yml, translated from benchmarks/sv-comp/dafny/array-cav19/array_tiling_tcpy.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_tiling_tcpy.c", 7, "reach_error"); }
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
  int S = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  S = __VERIFIER_nondet_int();
  assume_abort_if_not(S > 1);
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && S <= N && 2 * S <= N && N <= 268435455);
  int a[N];
  int acopy[N];
  while (i < S) {
    acopy[2 * S - (i + 1)] = a[2 * S - (i + 1)];
    acopy[i] = a[i];
    i = i + 1;
  }
  i = 0;
  while (i < 2 * S) {
    __VERIFIER_assert(acopy[i] == a[i]);
    i = i + 1;
  }
}

