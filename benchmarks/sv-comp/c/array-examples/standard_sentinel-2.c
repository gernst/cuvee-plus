// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_sentinel-2.c
// SV-COMP array-examples/standard_sentinel-2.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_sentinel-2.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_sentinel-2.c", 7, "reach_error"); }
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
  int marker = __VERIFIER_nondet_int();
  int pos = __VERIFIER_nondet_int();
  int i = __VERIFIER_nondet_int();
  int tmp = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 536870911);
  int a[N];
  assume_abort_if_not(0 < N);
  marker = __VERIFIER_nondet_int();
  pos = __VERIFIER_nondet_int();
  i = 0;
  while (i < N) {
    tmp = __VERIFIER_nondet_int();
    a[i] = tmp;
    i = i + 1;
  }
  if (pos >= 0 && pos < N) {
    a[pos] = marker;
    i = 0;
    while (a[i] != marker) {
      i = i + 1;
    }
    __VERIFIER_assert(i <= pos);
  }
}

