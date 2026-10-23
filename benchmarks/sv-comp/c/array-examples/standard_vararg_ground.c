// ./Cuvee.sh -teq -prove benchmarks/sv-comp/c/array-examples/standard_vararg_ground.c
// SV-COMP array-examples/standard_vararg_ground.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_vararg_ground.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_vararg_ground.c", 7, "reach_error"); }
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
  int a = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  assume_abort_if_not(0 < N);
  int aa[N];
  a = 0;
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    aa[i] = v;
    i = i + 1;
  }
  assume_abort_if_not(aa[N - 1] < 0);
  while (aa[a] >= 0) {
    a = a + 1;
  }
  x = 0;
  while (x < a) {
    __VERIFIER_assert(aa[x] >= 0);
    x = x + 1;
  }
}

