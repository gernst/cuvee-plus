// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-tiling/mlceu.c
// SV-COMP array-tiling/mlceu.yml, translated from benchmarks/sv-comp/dafny/array-tiling/mlceu.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "mlceu.c", 7, "reach_error"); }
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
  if (S <= 0) {
    return;
  }
  i = 0;
  int N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && S <= N && N <= 536870911);
  int a[N];
  while (i < S) {
    if (i / 65536 > 250) {
      a[i] = 1;
    } else {
      a[i] = 0;
    }
    i = i + 1;
  }
  i = 0;
  while (i < S) {
    __VERIFIER_assert(a[i] == 0);
    i = i + 1;
  }
}

