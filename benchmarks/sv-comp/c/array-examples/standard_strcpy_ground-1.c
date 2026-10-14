// ./Cuvee.sh -teq -simplify benchmarks/sv-comp/c/array-examples/standard_strcpy_ground-1.c
// SV-COMP array-examples/standard_strcpy_ground-1.yml, translated from benchmarks/sv-comp/dafny/array-examples/standard_strcpy_ground-1.dfy by ./Cuvee.sh -print c -known dfy,teq,rw

// the SV-COMP harness
extern void abort(void);
extern void __assert_fail(const char *, const char *, unsigned int, const char *) __attribute__ ((__nothrow__ , __leaf__)) __attribute__ ((__noreturn__));
void reach_error() { __assert_fail("0", "standard_strcpy_ground-1.c", 7, "reach_error"); }
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
  int j = __VERIFIER_nondet_int();
  int x = __VERIFIER_nondet_int();
  int v = __VERIFIER_nondet_int();
  assume_abort_if_not(0 <= N && N <= 268435455);
  assume_abort_if_not(0 < N);
  int src[N], dst[N];
  i = 0;
  j = 0;
  while (j < N) {
    v = __VERIFIER_nondet_int();
    src[j] = v;
    j = j + 1;
  }
  while (i < N && src[i] != 0) {
    dst[i] = src[i];
    i = i + 1;
  }
  x = 0;
  while (x < i) {
    __VERIFIER_assert(dst[x] == src[x]);
    x = x + 1;
  }
}

