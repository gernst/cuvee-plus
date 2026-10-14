// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-lopstr16/sum_multi_array.c
// SV-COMP array-lopstr16/sum_multi_array.yml, translated from benchmarks/sv-comp/dafny/array-lopstr16/sum_multi_array.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "sum_multi_array.c", 7, "reach_error"); }
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
  int v = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 134217727);
  assume_abort_if_not(0 < N);
  int a[N], b[N], c[N];
  i = 0;
  while (i < N) {
    v = __VERIFIER_nondet_int();
    a[i] = v;
    v = __VERIFIER_nondet_int();
    b[i] = v;
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    c[i] = a[i] + b[i];
    i = i + 1;
  }
  i = 0;
  while (i < N) {
    __VERIFIER_assert(c[i] == a[i] + b[i]);
    i = i + 1;
  }
}

