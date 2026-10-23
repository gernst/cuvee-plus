// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-industry-pattern/array_shadowinit.c
// SV-COMP array-industry-pattern/array_shadowinit.yml, translated from benchmarks/sv-comp/dafny/array-industry-pattern/array_shadowinit.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "array_shadowinit.c", 7, "reach_error"); }
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
  int i = __VERIFIER_nondet_int();
  int k = __VERIFIER_nondet_int();
  N = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  if (N > 0) {
    i = 0;
    k = 0;
    while (i < N) {
      a[k] = k;
      i = i + 1;
      k = k + 1;
    }
    i = 0;
    while (i < N) {
      __VERIFIER_assert(a[i] == i);
      i = i + 1;
    }
  }
}

